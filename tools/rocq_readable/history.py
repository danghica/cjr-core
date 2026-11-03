"""Cached Git evidence for prompts associated with declaration edits.

No semantic inference is made: all prompts added by a touching commit are
included. Line ranges are traced backwards, including edits without prompts.
"""
from __future__ import annotations

from collections import Counter
import difflib
import hashlib
import html
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


VERSION = 1
STAMP = re.compile(r"^\[(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d(?:\.\d+)?(?:Z|[+-]\d\d:\d\d))\]\n", re.M)
HUNK = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", re.M)


def git(repo, *args, input=None):
    return subprocess.run(["git", "--no-pager", "-C", str(repo), *args], input=input,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
                          timeout=60).stdout.decode("utf-8")


def records(text):
    matches = list(STAMP.finditer(text))
    result = []
    for i, match in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        body = text[match.end():end]
        # The logger appends two newlines after a prompt without a final newline.
        # Remove that framing only; keep embedded and additional blank lines.
        body = body.removesuffix("\n\n")
        result.append({"timestamp": match[1], "text": body})
    return result


def added_records(before, after):
    previous = Counter((p["timestamp"], p["text"]) for p in records(before))
    added = []
    for prompt in records(after):
        key = prompt["timestamp"], prompt["text"]
        if previous[key]:
            previous[key] -= 1
        else:
            added.append(prompt)
    return added


def patch_hunks(text):
    result = []
    for match in HUNK.finditer(text):
        old, old_count, new, new_count = match.groups()
        old_count, new_count = int(old_count or 1), int(new_count or 1)
        result.append([int(old) - bool(old_count), old_count,
                       int(new) - bool(new_count), new_count])
    return result


def text_hunks(before, after):
    return [[a, b - a, c, d - c] for tag, a, b, c, d in
            difflib.SequenceMatcher(None, before.splitlines(), after.splitlines(), autojunk=False).get_opcodes()
            if tag != "equal"]


def merge_ranges(ranges):
    result = []
    for a, b in sorted(ranges):
        if a >= b:
            continue
        if result and a <= result[-1][1]:
            result[-1][1] = max(b, result[-1][1])
        else:
            result.append([a, b])
    return result


def backwards(ranges, hunks):
    """Map zero-based half-open line ranges to the old side of a diff.

    A replacement extending outside the tracked declaration is ambiguous; do
    not pull adjacent definitions into its earlier history. Pure deletions
    count only inside a declaration, not on a neighbouring boundary.
    """
    mapped, touched, ambiguous = [], False, False
    for a, b in ranges:
        cursor, delta = a, 0
        for old, old_count, new, new_count in hunks:
            end = new + new_count
            if new > cursor:
                stop = min(new, b)
                if stop > cursor:
                    mapped.append([cursor + delta, stop + delta])
                    cursor = stop
            overlap = max(a, new) < min(b, end) if new_count else a < new < b
            if overlap:
                touched = True
                if old_count and new_count and (new < a or end > b):
                    ambiguous = True
                if old_count:
                    mapped.append([old, old + old_count])
            if new_count and end > a and new < b:
                cursor = max(cursor, min(end, b))
            delta = old + old_count - end
            if new >= b:
                break
        if cursor < b:
            mapped.append([cursor + delta, b + delta])
    return merge_ranges(mapped), touched, ambiguous


def blob(repo, revision, path):
    return git(repo, "show", f"{revision}:{path}")


def extract_commit(repo, commit, baseline=False):
    fields = git(repo, "show", "-s", "--format=%P%x00%cI%x00%s", commit).rstrip("\n").split("\0")
    parent = fields[0].split()[0] if fields[0] else None
    base = parent or git(repo, "hash-object", "-t", "tree", "--stdin", input=b"").strip()
    names = git(repo, "diff", "--no-ext-diff", "--no-textconv", "--name-status", "-z", "-M", base, commit).split("\0")
    changes, log_changed, i = [], False, 0
    while i < len(names) and names[i]:
        status, old = names[i:i + 2]
        i += 2
        new = names[i] if status.startswith(("R", "C")) else old
        if status.startswith(("R", "C")):
            i += 1
        log_changed |= new == "logs/prompts.txt"
        if not (new.endswith(".v") or old.endswith(".v")):
            continue
        patch = git(repo, "diff", "--no-ext-diff", "--no-textconv", "--no-color", "--unified=0", "-M",
                    base, commit, "--", old, new)
        changes.append({"old": None if status == "A" else old,
                        "new": None if status == "D" else new, "hunks": patch_hunks(patch)})
    prompts = []
    if log_changed and not baseline:
        try:
            before = blob(repo, parent, "logs/prompts.txt") if parent else ""
        except subprocess.CalledProcessError:
            before = ""
        try:
            prompts = added_records(before, blob(repo, commit, "logs/prompts.txt"))
        except subprocess.CalledProcessError:
            pass  # The log may have been deleted.
    return {"commit": commit, "date": fields[1], "subject": fields[2], "prompts": prompts, "changes": changes}


def update_stream(repo, previous, tip="HEAD", baseline=False):
    head = git(repo, "rev-parse", "--verify", tip).strip()
    shallow = git(repo, "rev-parse", "--is-shallow-repository").strip() == "true"
    if previous and previous.get("shallow") and not shallow:
        previous = None  # An unshallow fetch can reveal ancestors without moving HEAD.
    if previous and previous.get("head") == head:
        return previous
    lineage = git(repo, "rev-list", "--first-parent", "--reverse", head).splitlines()
    old_head = (previous or {}).get("head")
    if old_head in lineage:
        commits = previous["commits"][:]
        pending = lineage[lineage.index(old_head) + 1:]
    else:
        commits, pending = [], lineage
    for commit in pending:
        commits.append(extract_commit(repo, commit, baseline=baseline and commit == lineage[0]))
    return {"head": head, "commits": commits, "shallow": shallow}


def repository(path):
    path = path.resolve()
    try:
        return Path(git(path, "rev-parse", "--show-toplevel").strip())
    except (OSError, subprocess.SubprocessError):
        # Exported checkouts can still carry the checked-in history cache.
        return next((p for p in (path, *path.parents) if (p / "repository.json").is_file()), path)


def migration(repo):
    try:
        return json.loads((repo / "repository.json").read_text())["checkpoint"]
    except (OSError, ValueError, KeyError):
        return None


def bridge(repo, origin, checkpoint, primary):
    manifest = json.loads((origin / "migration-manifest.json").read_text())
    if manifest["checkpoint"] != checkpoint:
        raise ValueError("migration checkpoint mismatch")
    root_commit = primary["commits"][0]["commit"]
    paths = {c["new"] for c in primary["commits"][0]["changes"] if c["new"]}
    mapping = {}
    for entry in manifest["files"]:
        for destination in entry["destinations"]:
            prefix = repo.name + "/"
            if destination.startswith(prefix) and destination[len(prefix):] in paths:
                path = destination[len(prefix):]
                before = blob(origin, checkpoint, entry["source"])
                after = blob(repo, root_commit, path)
                mapping[path] = {"old": entry["source"], "hunks": text_hunks(before, after)}
    return {"checkpoint": checkpoint, "root": root_commit, "paths": mapping}


def declaration_ranges(source, decl):
    data = source.text.encode("utf-8")
    stop = decl.source_start + len(decl.source.encode("utf-8"))
    for span in decl.proof_spans:
        stop = max(stop, (span.get("loc") or {}).get("ep", stop))
    return [[data[:decl.source_start].count(b"\n"), data[:max(decl.source_start, stop - 1)].count(b"\n") + 1]]


def trace(path, ranges, commits, entries, skip_root=False):
    issues = []
    for commit in reversed(commits[1:] if skip_root else commits):
        change = next((c for c in commit["changes"] if c["new"] == path), None)
        if not change:
            continue
        ranges, touched, ambiguous = backwards(ranges, change["hunks"])
        if touched and commit["prompts"]:
            entries.append({k: commit[k] for k in ("commit", "date", "subject", "prompts")})
        if ambiguous:
            issues.append("Earlier attribution is ambiguous because a replacement crosses declaration boundaries.")
            return None, [], issues
        if change["old"] is None or not ranges:
            return None, [], issues
        path = change["old"]
    return path, ranges, issues


def read_cache(path):
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        if data.get("version") != VERSION or not isinstance(data.get("associations"), dict):
            raise ValueError("unsupported history cache")
        # Validate nested extraction data before using it for attribution.
        for name in ("primary", "origin"):
            stream = data.get(name)
            if name in data and not isinstance(stream, dict):
                raise ValueError("invalid history stream")
            if stream:
                if (not isinstance(stream["head"], str) or not isinstance(stream["shallow"], bool)
                        or not isinstance(stream["commits"], list) or not stream["commits"]):
                    raise ValueError("invalid history stream")
                for commit in stream["commits"]:
                    for key in ("commit", "date", "subject"):
                        if not isinstance(commit[key], str):
                            raise ValueError("invalid commit metadata")
                    for prompt in commit["prompts"]:
                        if not all(isinstance(prompt[k], str) for k in ("timestamp", "text")):
                            raise ValueError("invalid prompt record")
                    for change in commit["changes"]:
                        if not all(change[k] is None or isinstance(change[k], str) for k in ("old", "new")):
                            raise ValueError("invalid path")
                        if not all(len(h) == 4 and all(type(n) is int and n >= 0 for n in h) for h in change["hunks"]):
                            raise ValueError("invalid diff range")
        for saved in data["associations"].values():
            if (not isinstance(saved["entries"], list) or not isinstance(saved["issues"], list)
                    or not all(isinstance(s, str) for s in saved["issues"])):
                raise ValueError("invalid association issues")
            for entry in saved["entries"]:
                if not all(isinstance(entry[k], str) for k in ("commit", "date", "subject")):
                    raise ValueError("invalid association commit")
                for prompt in entry["prompts"]:
                    if not all(isinstance(prompt[k], str) for k in ("timestamp", "text")):
                        raise ValueError("invalid association prompt")
        mapping = data.get("bridge")
        if "bridge" in data and not isinstance(mapping, dict):
            raise ValueError("invalid migration bridge")
        if mapping:
            if not all(isinstance(mapping[k], str) for k in ("root", "checkpoint")):
                raise ValueError("invalid migration bridge")
            for path, change in mapping["paths"].items():
                if not isinstance(path, str) or not isinstance(change["old"], str):
                    raise ValueError("invalid migration path")
                if not all(len(h) == 4 and all(type(n) is int and n >= 0 for n in h) for h in change["hunks"]):
                    raise ValueError("invalid migration diff")
        return data
    except (OSError, ValueError, KeyError, TypeError, AttributeError):
        return {"version": VERSION, "associations": {}}


def atomic_cache(path, data):
    encoded = json.dumps(data, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    if path.is_file() and path.read_text(encoding="utf-8") == encoded:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                         prefix=".history-", delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(encoded)
        os.replace(temporary, path)
    finally:
        if temporary:
            temporary.unlink(missing_ok=True)


def validate_cache_path(path):
    if path.suffix != ".json" or path.name.endswith("explanations.json"):
        raise ValueError("history cache must be a separate .json file, not an explanation cache")
    try:
        existing = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return
    if isinstance(existing, dict) and any(k in existing for k in ("entries", "explanations", "rules")):
        raise ValueError("history cache path contains explanation, report, or dictionary data; choose a separate file")


def collect(sources, cache=None, history_repository=None):
    """Return per-declaration history without reading or writing explanation data."""
    if not sources:
        return {}
    repo = repository(sources[0].root)
    cache = Path(cache) if cache else repo / "build/prompt-history.json"
    validate_cache_path(cache)
    data = read_cache(cache)
    problems = []
    checkpoint = migration(repo)
    try:
        data["primary"] = update_stream(repo, data.get("primary"), baseline=bool(checkpoint))
    except (OSError, subprocess.SubprocessError):
        problems.append("Git history is unavailable; showing cached evidence where available.")
    primary = data.get("primary")
    if primary and primary["shallow"]:
        problems.append("The checkout is shallow; earlier commits may be missing.")
    if checkpoint and primary:
        origin = Path(history_repository) if history_repository else repo.parent
        cached_bridge = data.get("bridge", {})
        if (cached_bridge.get("checkpoint") != checkpoint or
                cached_bridge.get("root") != primary["commits"][0]["commit"]):
            data.pop("bridge", None)
            data.pop("origin", None)
        if not data.get("bridge"):
            try:
                origin_stream = update_stream(origin, None, checkpoint)
                migration_bridge = bridge(repo, origin, checkpoint, primary)
                data.update(origin=origin_stream, bridge=migration_bridge)
            except (OSError, ValueError, KeyError, subprocess.SubprocessError):
                problems.append("Pre-split history is unavailable; supply --history-repository with the original checkout.")
        elif data.get("origin", {}).get("shallow"):
            try:
                data["origin"] = update_stream(origin, data["origin"], checkpoint)
            except (OSError, subprocess.SubprocessError):
                pass
        if data.get("origin", {}).get("shallow"):
            problems.append("The original checkout was shallow when history was cached.")
    result = {}
    for source in sources:
        path = source.path.resolve().relative_to(repo).as_posix()
        digest = hashlib.sha256(source.text.encode()).hexdigest()
        for decl in source.declarations:
            ranges = declaration_ranges(source, decl)
            revisions = [[s.get("head"), len(s.get("commits", [])), s.get("shallow")]
                         for s in (primary or {}, data.get("origin") or {})]
            signature = [path, digest, ranges, revisions, data.get("bridge")]
            key = decl.identity + ":" + hashlib.sha256(json.dumps(signature, sort_keys=True).encode()).hexdigest()
            saved = data["associations"].get(key)
            if saved and isinstance(saved, dict) and isinstance(saved.get("entries"), list) and isinstance(saved.get("issues"), list):
                record = saved
            else:
                entries, issues = [], []
                tracked_path = path
                if primary:
                    try:
                        head_text = blob(repo, primary["head"], path)
                        ranges, _, ambiguous = backwards(ranges, text_hunks(head_text, source.text))
                        if ambiguous:
                            issues.append("Uncommitted changes prevent reliable mapping to the committed definition.")
                            ranges = []
                        elif not ranges:
                            issues.append("This definition has no committed counterpart yet.")
                    except (OSError, subprocess.SubprocessError):
                        issues.append("Cannot map this source to its committed version.")
                        ranges = []
                    if ranges:
                        tracked_path, ranges, trace_issues = trace(path, ranges, primary["commits"], entries, skip_root=bool(checkpoint))
                        issues.extend(trace_issues)
                    if checkpoint and tracked_path and ranges:
                        mapping = data.get("bridge", {}).get("paths", {}).get(tracked_path)
                        if mapping and data.get("origin"):
                            ranges, _, ambiguous = backwards(ranges, mapping["hunks"])
                            if ambiguous:
                                issues.append("Migration edits prevent reliable earlier attribution.")
                            elif ranges:
                                _, _, trace_issues = trace(mapping["old"], ranges, data["origin"]["commits"], entries)
                                issues.extend(trace_issues)
                        else:
                            issues.append("No original history mapping is available for this file.")
                record = {"entries": entries, "issues": issues}
                # Keep other output directories' declarations, but discard stale
                # versions of this declaration after source or ancestry changes.
                for stale in [k for k in data["associations"] if k.startswith(decl.identity + ":")]:
                    del data["associations"][stale]
                data["associations"][key] = record
            issues = list(dict.fromkeys([*problems, *record["issues"]]))
            result[decl.identity] = {"entries": record["entries"], "issues": issues, "complete": not issues}
    try:
        atomic_cache(cache, data)
    except OSError:
        for record in result.values():
            record["issues"].append("History cache could not be saved.")
            record["complete"] = False
    return result


def panel(record=None):
    record = record or {"entries": [], "issues": ["History has not been extracted."], "complete": False}
    body = '<details class="prompt-history"><summary>History</summary>'
    body += '<p class="notice">Prompts are associated by commit: all prompts added in a commit that touched this declaration or its proof are included.</p>'
    if not record["complete"]:
        body += '<p class="notice">History incomplete: ' + html.escape(" ".join(record["issues"])) + '</p>'
    if not record["entries"]:
        body += '<p class="meta">No recorded prompts found.</p>'
    for entry in record["entries"]:
        body += '<section class="history-entry"><h3>' + html.escape(entry["subject"]) + '</h3>'
        body += '<p class="meta">Commit <code>' + html.escape(entry["commit"][:12]) + '</code> · ' + html.escape(entry["date"]) + '</p>'
        for number, prompt in enumerate(entry["prompts"], 1):
            body += '<details class="history-prompt-disclosure"><summary>Prompt ' + str(number) + ' · ' + html.escape(prompt["timestamp"]) + '</summary>'
            body += '<pre class="history-prompt" style="white-space:pre-wrap;overflow-wrap:anywhere">' + html.escape(prompt["text"]) + '</pre>'
            body += '</details>'
        body += '</section>'
    return body + '</details>'
