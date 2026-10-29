"""Small, bounded JSON-RPC client for the pinned coq-lsp AST protocol."""
from __future__ import annotations

import json
import os
from pathlib import Path
import queue
import shutil
import subprocess
import tempfile
import threading
import time


class BackendError(RuntimeError):
    pass


def executable() -> str:
    found = shutil.which("coq-lsp")
    if found:
        return found
    # opam need not have been activated in the invoking shell.
    candidate = Path.home() / ".opam/default/bin/coq-lsp"
    if candidate.is_file():
        return str(candidate)
    raise BackendError("coq-lsp is missing; install coq-lsp.0.2.5+8.20 and activate its opam switch")


class Backend:
    def __init__(self, workspace: Path, timeout: float = 600, binary: str | None = None):
        self.workspace = workspace
        self.timeout = timeout
        self.sequence = 0
        self.messages: queue.Queue = queue.Queue()
        self.diagnostics: dict[str, list] = {}
        self.stderr = tempfile.TemporaryFile()
        binary = binary or executable()
        try:
            version = subprocess.run([binary, "--version"], capture_output=True, text=True,
                                     timeout=10, check=True).stdout.strip()
        except (OSError, subprocess.SubprocessError) as exc:
            self.stderr.close()
            raise BackendError(f"cannot determine coq-lsp version: {exc}") from exc
        if version != "0.2.5":
            self.stderr.close()
            raise BackendError(f"unsupported coq-lsp version {version!r}; require 0.2.5+8.20")
        env = os.environ.copy()
        env["PATH"] = str(Path(binary).parent) + os.pathsep + env.get("PATH", "")
        try:
            self.process = subprocess.Popen([binary], cwd=workspace, env=env,
                                            stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                            stderr=self.stderr)
        except OSError as exc:
            self.stderr.close()
            raise BackendError(str(exc)) from exc
        self.reader = threading.Thread(target=self._read, daemon=True)
        self.reader.start()
        try:
            self.request("initialize", {
                "processId": os.getpid(), "rootUri": workspace.as_uri(),
                "workspaceFolders": [{"uri": workspace.as_uri(), "name": workspace.name}],
                "capabilities": {},
                "initializationOptions": {"client_version": "0.2.5", "check_only_on_request": True,
                                          "admit_on_bad_qed": False, "max_errors": 1000,
                                          "eager_diagnostics": False, "send_perf_data": False},
            })
            self.notify("initialized", {})
        except BaseException:
            self.close()
            raise

    @property
    def versions(self):
        return getattr(self, "_versions", {})

    def _read(self):
        try:
            while True:
                headers = {}
                while True:
                    line = self.process.stdout.readline()
                    if not line:
                        raise EOFError("coq-lsp closed its output")
                    if line in (b"\r\n", b"\n"):
                        break
                    key, value = line.decode("ascii").split(":", 1)
                    headers[key.lower()] = value.strip()
                length = int(headers["content-length"])
                chunks = bytearray()
                while len(chunks) < length:
                    chunk = self.process.stdout.read(length - len(chunks))
                    if not chunk:
                        raise EOFError("truncated JSON-RPC response")
                    chunks.extend(chunk)
                self.messages.put(json.loads(chunks))
        except Exception as exc:
            self.messages.put(BackendError(str(exc)))

    def _send(self, message):
        data = json.dumps({"jsonrpc": "2.0", **message}, ensure_ascii=False).encode()
        try:
            self.process.stdin.write(f"Content-Length: {len(data)}\r\n\r\n".encode() + data)
            self.process.stdin.flush()
        except (OSError, ValueError) as exc:
            raise BackendError(f"cannot communicate with coq-lsp: {exc}") from exc

    def notify(self, method, params):
        self._send({"method": method, "params": params})

    def request(self, method, params):
        self.sequence += 1
        request_id = self.sequence
        self._send({"id": request_id, "method": method, "params": params})
        deadline = time.monotonic() + self.timeout
        while True:
            try:
                message = self.messages.get(timeout=max(0, deadline - time.monotonic()))
            except queue.Empty as exc:
                raise BackendError(f"coq-lsp timed out after {self.timeout:g}s during {method}") from exc
            if isinstance(message, Exception):
                raise message
            if message.get("method") == "$/coq/serverVersion":
                self._versions = message["params"]
                if not self._versions.get("coq", "").startswith("8.20"):
                    raise BackendError(f"unsupported Coq version: {self._versions}")
            if message.get("method") == "textDocument/publishDiagnostics":
                self.diagnostics[message["params"]["uri"]] = message["params"]["diagnostics"]
            if "method" in message and "id" in message:
                self._send({"id": message["id"], "result": None})
            if message.get("id") == request_id:
                if "error" in message:
                    raise BackendError(f"{method}: {message['error'].get('message', message['error'])}")
                return message.get("result")

    def document(self, path: Path, source: str, selected=None, model=None):
        uri = path.as_uri()
        self.notify("textDocument/didOpen", {"textDocument": {
            "uri": uri, "languageId": "coq", "version": 1, "text": source}})
        from .project import Source
        from .ast import declarations
        data = source.encode()
        model = model or Source.load(path, self.workspace)
        glob = model.glob
        candidates = [(offset, name) for offset, (name, kind) in glob.definitions.items()
                      if selected and kind not in ("binder", "var") and
                      (name == selected or name.split(".")[-1] == selected)]
        if len(candidates) > 1:
            raise BackendError("ambiguous declaration: " + ", ".join(name for _, name in candidates))
        offset = candidates[0][0] if candidates else (len(source[:1].encode()) if selected else len(data))
        spans = []
        while True:
            prefix = data[:offset].decode()
            lines = prefix.split("\n")
            position = {"line": len(lines) - 1, "character": len(lines[-1].encode("utf-16-le")) // 2}
            goals = self.request("proof/goals", {"textDocument": {"uri": uri, "version": 1}, "position": position})
            if not selected:
                result = self.request("coq/getDocument", {"textDocument": {"uri": uri, "version": 1}, "ast": True})
                return result, self.diagnostics.get(uri, [])
            try:
                ast = self.request("petanque/ast_at_pos", {"uri": uri, "position": position})
            except BackendError as exc:
                if "No node at point" not in str(exc) or offset >= len(data):
                    raise
                # Comments/whitespace aren't syntax nodes. Advance a Unicode
                # character, without implementing a second Rocq lexer.
                offset += len(data[offset:].decode()[0].encode())
                continue
            if ast:
                spans.append({"ast": ast})
            # Without a fresh .glob, advance through Rocq-provided sentence
            # ranges, stopping immediately after the chosen declaration.
            selection = Source(path, model.root, source, model.module, glob)
            declarations(selection, {"spans": spans})
            if candidates or any(d.name == selected or d.identity == selected for d in selection.declarations):
                if not ast:
                    raise BackendError("Rocq could not parse the selected declaration")
                prefix = data[:ast["loc"]["ep"]].decode()
                self.notify("textDocument/didChange", {"textDocument": {"uri": uri, "version": 2},
                            "contentChanges": [{"text": prefix}]})
                lines = prefix.split("\n")
                self.request("proof/goals", {"textDocument": {"uri": uri, "version": 2},
                             "position": {"line": len(lines) - 1, "character": len(lines[-1].encode("utf-16-le")) // 2}})
                result = self.request("coq/getDocument", {"textDocument": {"uri": uri, "version": 2}, "ast": True})
                return result, self.diagnostics.get(uri, [])
            ends = [(span.get("ast", {}).get("loc") or {}).get("ep", 0) for span in spans]
            new_offset = max([offset, *ends])
            while new_offset < len(data) and chr(data[new_offset]).isspace():
                new_offset += 1
            if new_offset <= offset or new_offset >= len(data):
                raise BackendError(f"declaration {selected!r} not found before a parse error or end of source")
            offset = new_offset + len(data[new_offset:].decode()[0].encode())

    def close_document(self, path):
        self.notify("textDocument/didClose", {"textDocument": {"uri": path.as_uri()}})

    def close(self):
        if self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.wait(timeout=3)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait(timeout=3)
        self.process.stdin.close()
        self.process.stdout.close()
        self.reader.join(timeout=1)
        self.stderr.close()

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()
