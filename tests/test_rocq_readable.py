"""Behavior tests using real Rocq ASTs, plus filesystem/template invariants."""
from __future__ import annotations

from contextlib import redirect_stderr, redirect_stdout
import hashlib
from html.parser import HTMLParser
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch
from urllib.parse import unquote, urlparse

from tools.rocq_readable.ast import Adapter, Declaration, declarations
from tools.rocq_readable.backend import Backend, BackendError, executable
from tools.rocq_readable.cli import DEFAULT_DICTIONARY, generate, learning, main, prepare
from tools.rocq_readable.dictionary import Dictionary, DictionaryError, validate
from tools.rocq_readable.dependencies import Graph, build_graph, root_entries
from tools.rocq_readable.explanations import Options, StartupBlocked, explain, query
from tools.rocq_readable.layout import Doc, Token, anchor, leaf
from tools.rocq_readable.project import Glob, Source, configuration, discover


ROOT = Path(__file__).resolve().parents[1]


class HTMLInventory(HTMLParser):
    def __init__(self, text):
        super().__init__()
        self.ids, self.links = [], []
        self.dependency_data, self.in_dependency_data = "", False
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == "script":
            self.in_dependency_data = attrs.get("id") == "dependency-data"
        if "id" in attrs:
            self.ids.append(attrs["id"])
        if "href" in attrs:
            self.links.append(attrs["href"])

    def handle_data(self, text):
        if self.in_dependency_data:
            self.dependency_data += text

    def handle_endtag(self, tag):
        if tag == "script":
            self.in_dependency_data = False


def audit_links(output):
    inventories = {p.resolve(): HTMLInventory(p.read_text()) for p in output.rglob("*.html")}
    for path, inventory in inventories.items():
        if len(set(inventory.ids)) != len(inventory.ids):
            raise AssertionError(f"duplicate anchors in {path}")
        for link in inventory.links:
            url = urlparse(link)
            if url.scheme or url.netloc:
                raise AssertionError(f"external link {link}")
            target = (path.parent / unquote(url.path)).resolve() if url.path else path
            if not target.is_relative_to(output.resolve()) or not target.exists():
                raise AssertionError(f"missing/outside destination {link} in {path}")
            if url.fragment and unquote(url.fragment) not in inventories[target].ids:
                raise AssertionError(f"missing anchor {link} in {path}")


class FilesystemAndRules(unittest.TestCase):
    def test_discover_unlisted_hidden_nested_and_boundary(self):
        with tempfile.TemporaryDirectory() as tmp, tempfile.TemporaryDirectory() as outside:
            root = Path(tmp)
            (root / "_CoqProject").write_text("listed.v\n")
            for name in ["listed.v", "unlisted.v", "nested/a.v", ".hidden/b.v", "output/omit.v", ".git/omit.v"]:
                p = root / name
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text("Definition x := 0.\n")
            external = Path(outside) / "external.v"
            external.write_text("Definition x := 1.\n")
            (root / "external").symlink_to(outside, target_is_directory=True)
            (root / "linked.v").symlink_to(external)
            self.assertEqual([str(p.relative_to(root)) for p in discover(root, root / "output")],
                             [".hidden/b.v", "listed.v", "nested/a.v", "unlisted.v"])
            (root / "nested/_RocqProject").write_text("-Q . Nested\n")
            self.assertEqual(configuration(root / "nested/a.v", root), root / "nested/_RocqProject")

    def test_glob_must_match_source_digest(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "a.v"
            data = b"Definition x := 0.\n"
            path.with_suffix(".glob").write_text("DIGEST " + hashlib.md5(data).hexdigest() + "\nFA\ndef 11:11 <> x\n")
            self.assertTrue(Glob.load(path, data).valid)
            self.assertFalse(Glob.load(path, data + b"\n").valid)

    def test_changed_project_dependency_invalidates_resolution_data(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "_CoqProject").write_text("-Q . P\n")
            (root / "A.v").write_text("Definition x := 0.\n")
            (root / "A.vo").write_bytes(b"compiled dependency")
            path = root / "B.v"
            data = b"From P Require Import A.\nDefinition y := A.x.\n"
            path.write_bytes(data)
            glob = path.with_suffix(".glob")
            glob.write_text("DIGEST " + hashlib.md5(data).hexdigest() + "\nFP.B\nR22:22 P.A <> <> lib\ndef 35:35 <> y\n")
            self.assertTrue(Source.load(path, root).glob.valid)
            newer = glob.stat().st_mtime + 2
            os.utime(root / "A.vo", (newer, newer))
            self.assertFalse(Source.load(path, root).glob.valid)

    def test_template_validation_and_scope_matching(self):
        base = {"kind": "notation", "key": "_ + _", "arity": 2, "label": "add"}
        for bad in ([0], [0, 0], [0, 1, 2], [True, 1]):
            with self.assertRaises(DictionaryError):
                validate({**base, "slots": bad})
        with tempfile.TemporaryDirectory() as tmp:
            dictionary = Dictionary(Path(tmp) / "rules.json")
            dictionary.replace({**base, "scope": "nat_scope", "slots": [1, 0]})
            dictionary.save()
            restored = Dictionary(dictionary.path)
            self.assertIsNone(restored.match("notation", "_ + _", 2, "type_scope"))
            rule = restored.match("notation", "_ + _", 2, "nat_scope")
            rendered = restored.apply(rule, Token("+", identity="Project.add"), [leaf("a"), leaf("b")])
            self.assertEqual(rendered.plain(), "add(b, a)")
            self.assertEqual(rendered.label.identity, "Project.add")
            restored.remove(rule)
            restored.save()
            self.assertEqual(Dictionary(dictionary.path).rules, [])
            dictionary.path.write_text('{"version":2,"rules":[]}')
            with self.assertRaises(DictionaryError):
                Dictionary(dictionary.path)

    def test_notation_identity_prevents_cross_module_rule_reuse(self):
        with tempfile.TemporaryDirectory() as tmp:
            dictionary = Dictionary(Path(tmp) / "rules.json")
            dictionary.replace({"kind":"notation", "key":"_ ∗ _", "arity":2,
                                "label":"separately", "scope":"bi_scope", "identity":"Iris.sep"})
            self.assertIsNotNone(dictionary.match("notation", "_ ∗ _", 2, "bi_scope", identity="Iris.sep"))
            self.assertIsNone(dictionary.match("notation", "_ ∗ _", 2, "bi_scope", identity="User.multiply"))

    def test_unresolved_short_reference_does_not_guess_a_project_symbol(self):
        source = Source(Path("/tmp/A.v"), Path("/tmp"), "value", "Project.A", Glob())
        adapter = Adapter(source, Dictionary(DEFAULT_DICTIONARY), {"Project.A.value"})
        node = {"v": ["Ser_Qualid", ["DirPath", []], ["Id", "value"]], "loc": {"bp": 0, "ep": 5}}
        self.assertEqual(adapter.ref(node, {}).identity, "value")

    def test_backend_versions_crashes_and_timeouts_are_reported(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fake = root / "coq-lsp"
            fake.write_text('#!/usr/bin/env python3\nprint("99.0")\n')
            fake.chmod(0o755)
            with self.assertRaisesRegex(BackendError, "unsupported coq-lsp"):
                Backend(root, binary=str(fake))
            fake.write_text('#!/usr/bin/env python3\nimport sys,time\nif "--version" in sys.argv: print("0.2.5")\nelse: time.sleep(10)\n')
            with self.assertRaisesRegex(BackendError, "timed out"):
                Backend(root, timeout=.1, binary=str(fake))
            fake.write_text('#!/usr/bin/env python3\nimport sys\nif "--version" in sys.argv: print("0.2.5")\n')
            with self.assertRaisesRegex(BackendError, "closed its output"):
                Backend(root, timeout=1, binary=str(fake))

    def test_inline_and_multiline_scope(self):
        self.assertEqual(Doc(Token("f"), [leaf("x"), leaf("y")]).plain(), "f(x, y)")
        document = Doc(Token("forall"), [Doc(Token("body"), [leaf("x")], block=True)], block=True)
        self.assertEqual(document.plain(), "forall:\n    body:\n        x")
        self.assertNotIn("(", document.plain())
        long_call = Doc(Token("f"), [leaf("x" * 60), leaf("y" * 60)]).plain()
        self.assertTrue(long_call.startswith("f:\n    "))
        self.assertNotIn("(", long_call)
        self.assertTrue(anchor("A.Σ").isascii())

    def test_html_escapes_source_and_template_labels(self):
        from tools.rocq_readable.layout import render_html
        document = Doc(Token('<script>alert("x")</script>'), [leaf("a < b & c")])
        rendered = render_html(document, Path("/tmp/a.html"), {})
        self.assertNotIn("<script>", rendered)
        self.assertIn("&lt;script&gt;", rendered)
        self.assertIn("&amp;", rendered)

    def test_learning_preview_save_reject_remove_and_cancel(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            dictionary = Dictionary(root / "rules.json")
            encounters = {("application", "P.f", 2, None, None): (Token("f", identity="P.f"), [leaf("a"), leaf("b")], "f a b")}
            with patch("builtins.input", side_effect=["1", '{"label":"pair","slots":[0]}', "1", '{"label":"pair","slots":[0,1]}', "n", "1", '{"label":"pair","slots":[1,0]}', "y", "done"]), redirect_stdout(io.StringIO()):
                learning(dictionary, encounters, root / "out")
            self.assertTrue((root / "out/rule-preview.html").exists())
            self.assertEqual(Dictionary(dictionary.path).rules[0]["slots"], [1, 0])
            with patch("builtins.input", side_effect=["remove 1", "y", "done"]), redirect_stdout(io.StringIO()):
                learning(dictionary, encounters, root / "out")
            self.assertEqual(Dictionary(dictionary.path).rules, [])
            with patch("builtins.input", side_effect=EOFError), redirect_stdout(io.StringIO()):
                learning(dictionary, encounters, root / "out")


def backend_available():
    try:
        return bool(executable())
    except BackendError:
        return False


class DependencyAndExplanationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.source = Source(self.root / "A.v", self.root, "Definition a := 0.", "P.A", Glob())
        self.source.declarations = [Declaration("a", "P.A.a", "definition", {}, "Definition a := 0.")]
        self.sources = [self.source]
        self.documents = {self.source.path: [leaf("definition a: 0")]}
        self.graph = Graph({"P.A.a": []}, {"P.A.a": []}, ["P.A.a"])
        self.cache = self.root / "cache.json"

    def test_roots_cover_shared_cycles_and_disconnected_components(self):
        edges = {"a": ["b"], "b": ["a", "c"], "c": ["d"], "d": ["c"],
                 "isolated": [], "consumer1": ["shared"], "consumer2": ["shared"], "shared": [], "self": ["self"]}
        self.assertEqual(root_entries(edges), ["a", "consumer1", "consumer2", "isolated", "self"])
        # Large chains must not depend on Python's recursive call limit.
        chain = {str(i): [str(i + 1)] for i in range(2000)}
        chain["2000"] = []
        self.assertEqual(root_entries(chain), ["0"])

    def test_diagram_data_preserves_shared_nodes_cycles_and_destinations(self):
        from tools.rocq_readable.html import index
        self.source.declarations.extend([Declaration("b", "P.A.b", "lemma", {}, ""), Declaration("shared", "P.A.shared", "definition", {}, "")])
        graph = Graph({"P.A.a": ["P.A.shared"], "P.A.b": ["P.A.shared"], "P.A.shared": ["P.A.shared"]},
                      {i: [] for i in ("P.A.a", "P.A.b", "P.A.shared")}, ["P.A.a", "P.A.b"])
        output = self.root / "html"
        body = index(self.sources, {self.source.path: output / "A.html"}, output, graph)
        data = json.loads(HTMLInventory(body).dependency_data)
        self.assertEqual(len(data), 3)
        for identity, dependencies in graph.edges.items():
            self.assertEqual(data[identity]["dependencies"], dependencies)
            self.assertEqual(data[identity]["href"], "A.html#" + anchor(identity))
            self.assertEqual(data[identity]["file"], "A.v")
        self.assertEqual(data["P.A.b"]["name"], "b")
        self.assertEqual(data["P.A.b"]["kind"], "lemma")

    def test_diagram_labels_cannot_break_out_of_embedded_json(self):
        from tools.rocq_readable.html import index
        label = '</script><img src=x onerror="alert(1)">'
        self.source.declarations[0].name = label
        output = self.root / "html"
        body = index(self.sources, {self.source.path: output / "A.html"}, output, self.graph)
        data = json.loads(HTMLInventory(body).dependency_data)
        self.assertEqual(data["P.A.a"]["name"], label)
        self.assertNotIn(label, body)
        self.assertNotIn("<img", body)

    def test_file_graph_contains_only_included_entries_and_local_links(self):
        from tools.rocq_readable.html import page
        other = Declaration("shared", "P.A.shared", "lemma", {}, "")
        self.source.declarations.append(other)
        external = "P.B.external"
        graph = Graph({"P.A.a": [other.identity, external], other.identity: ["P.A.a"], external: []},
                      {"P.A.a": [], other.identity: [], external: []}, ["P.A.a"])
        current = self.root / "html/A.html"
        symbols = {"P.A.a": (current, anchor("P.A.a")), other.identity: (current, anchor(other.identity)),
                   external: (current.parent / "B.html", anchor(external))}
        body = page(self.source, [leaf("a"), leaf("shared")], current, current.parent, symbols, [], graph=graph)
        parsed = HTMLInventory(body)
        data = json.loads(parsed.dependency_data)
        self.assertEqual(set(data), {"P.A.a", other.identity})
        self.assertEqual(data["P.A.a"]["dependencies"], [other.identity])
        self.assertEqual(data[other.identity]["dependencies"], ["P.A.a"])
        self.assertEqual(data["P.A.a"]["href"], "#" + anchor("P.A.a"))
        self.assertIn('B.html#' + anchor(external), body)
        self.assertLess(body.index('id="dependency-svg"'), body.index('<article '))
        self.assertEqual(len(parsed.ids), len(set(parsed.ids)))
        self.assertNotIn('value="files"', body)

    def test_glob_includes_context_proofs_and_normalizes_fields(self):
        decl = self.source.declarations[0]
        child = Declaration("field", "P.A.a.field", "field", {}, "")
        decl.children = [child]
        decl.context = [{"loc": {"bp": 40, "ep": 50}}]
        decl.proof_spans = [{"loc": {"bp": 60, "ep": 90}}]
        decl.proof_complete = True
        other = Source(self.root / "B.v", self.root, "", "P.B", Glob())
        other.declarations = [Declaration("b", "P.B.b", "lemma", {}, ""), Declaration("c", "P.B.c", "definition", {}, "")]
        self.source.glob = Glob(valid=True, references={
            3: (4, "P.A.a.field", "proj"), 42: (43, "P.B.c", "def"),
            62: (63, "P.B.b", "thm"), 70: (71, "P.B.b", "thm"),
            75: (76, "P.B.c", "var"), 92: (93, "P.B.missing", "thm")})
        graph = build_graph([self.source, other], {self.source.path: [leaf("a")], other.path: [leaf("b"), leaf("c")]}, {})
        self.assertEqual(graph.edges[decl.identity], ["P.A.a", "P.B.b", "P.B.c"])
        self.assertEqual(graph.roots, ["P.A.a"])

    def test_cache_reuse_context_and_model_invalidation(self):
        options = Options("auto", "model-a", cache=self.cache)
        with patch("tools.rocq_readable.explanations.shutil.which", return_value="codex"), \
             patch("tools.rocq_readable.explanations.query", return_value="Defines zero.") as model:
            first = explain(self.sources, self.documents, self.graph, options)
            cached = explain(self.sources, self.documents, self.graph, options)
            self.assertEqual(first, cached)
            self.assertEqual(model.call_count, 1)
            options.model = "model-b"
            explain(self.sources, self.documents, self.graph, options)
            self.source.declarations[0].source = "Definition a := 1."
            explain(self.sources, self.documents, self.graph, options)
            self.assertEqual(model.call_count, 3)
        options.mode = "offline"
        with patch("tools.rocq_readable.explanations.query") as model:
            self.assertEqual(explain(self.sources, self.documents, self.graph, options)["P.A.a"]["description"], "Defines zero.")
            model.assert_not_called()
        self.assertFalse(list(self.root.glob(".explanations-*")))

    def test_dependency_context_invalidates_cache(self):
        second = Declaration("b", "P.A.b", "definition", {}, "Definition b := 0.")
        self.source.declarations.append(second)
        self.documents[self.source.path].append(leaf("b"))
        self.graph = Graph({"P.A.a": ["P.A.b"], "P.A.b": []}, {"P.A.a": [], "P.A.b": []}, ["P.A.a"])
        with patch("tools.rocq_readable.explanations.shutil.which", return_value="codex"), \
             patch("tools.rocq_readable.explanations.query", return_value="Text.") as model:
            options = Options("auto", cache=self.cache)
            explain(self.sources, self.documents, self.graph, options)
            second.source = "Definition b := 1."
            explain(self.sources, self.documents, self.graph, options)
            self.assertEqual(model.call_count, 4)
            self.assertIn("dependencies", model.call_args.args[1])

    def test_offline_missing_cli_and_failed_requests(self):
        result = explain(self.sources, self.documents, self.graph, Options(cache=self.cache))
        self.assertEqual(result["P.A.a"]["status"], "unavailable")
        with patch("tools.rocq_readable.explanations.shutil.which", return_value=None):
            self.assertEqual(explain(self.sources, self.documents, self.graph, Options("auto", cache=self.cache))["P.A.a"]["status"], "unavailable")
        for failure in [subprocess.TimeoutExpired("codex", 1), subprocess.CalledProcessError(1, "codex", stderr="SECRET"), ValueError("SECRET")]:
            with self.subTest(failure=type(failure)), patch("tools.rocq_readable.explanations.shutil.which", return_value="codex"), \
                 patch("tools.rocq_readable.explanations.query", side_effect=failure):
                result = explain(self.sources, self.documents, self.graph, Options("auto", cache=self.cache))
                self.assertEqual(result["P.A.a"]["status"], "failed")
                self.assertNotIn("SECRET", json.dumps(result))
        self.cache.write_text('{"version":99,"entries":{}}')
        result = explain(self.sources, self.documents, self.graph, Options(cache=self.cache))
        self.assertEqual(result["P.A.a"]["status"], "failed")
        self.assertEqual(json.loads(self.cache.read_text())["version"], 99)

    def test_query_uses_stdin_isolation_and_validated_plain_text(self):
        def run(command, **kwargs):
            self.assertIsInstance(command, list)
            self.assertEqual(command[-1], "-")
            self.assertNotEqual(kwargs["cwd"], self.root)
            self.assertEqual(command[command.index("--sandbox") + 1], "read-only")
            self.assertEqual(command[command.index("--ask-for-approval") + 1], "never")
            self.assertIn("--ephemeral", command)
            self.assertIn("shell_tool", command)
            self.assertEqual(command[command.index("--model") + 1], "model")
            self.assertIn("$(malicious)", kwargs["input"])
            self.assertTrue(hasattr(kwargs["stderr"], "write"))
            result = Path(command[command.index("--output-last-message") + 1])
            result.write_text('{"description":"<script>text</script>"}')
            return subprocess.CompletedProcess(command, 0)
        with patch("tools.rocq_readable.explanations.subprocess.run", side_effect=run):
            self.assertEqual(query("codex", {"declaration": "$(malicious)"}, Options(model="model")), "<script>text</script>")
        def malformed(command, **kwargs):
            Path(command[command.index("--output-last-message") + 1]).write_text('{"description":"", "extra":"bad"}')
        with patch("tools.rocq_readable.explanations.subprocess.run", side_effect=malformed):
            with self.assertRaises(ValueError):
                query("codex", {}, Options())

    def test_query_identifies_sandbox_startup_failure_without_leaking_diagnostics(self):
        def blocked(command, **kwargs):
            kwargs["stderr"].write(b"SECRET\nError: failed to initialize in-process app-server client: Operation not permitted (os error 1)\n")
            raise subprocess.CalledProcessError(1, command)
        with patch("tools.rocq_readable.explanations.subprocess.run", side_effect=blocked):
            with self.assertRaises(StartupBlocked) as caught:
                query("codex", {}, Options())
        self.assertIn("enclosing sandbox", str(caught.exception))
        self.assertNotIn("SECRET", str(caught.exception))

    def test_unrelated_permission_warning_does_not_mask_other_startup_errors(self):
        def failed(command, **kwargs):
            kwargs["stderr"].write(b"WARNING: PATH aliases: Operation not permitted\nError: failed to initialize in-process app-server client: connection refused\n")
            raise subprocess.CalledProcessError(1, command)
        with patch("tools.rocq_readable.explanations.subprocess.run", side_effect=failed):
            with self.assertRaises(subprocess.CalledProcessError):
                query("codex", {}, Options())

    def test_startup_failure_stops_repeated_requests(self):
        second = Declaration("b", "P.A.b", "definition", {}, "Definition b := 0.")
        self.source.declarations.append(second)
        self.documents[self.source.path].append(leaf("b"))
        self.graph = Graph({"P.A.a": [], "P.A.b": []}, {"P.A.a": [], "P.A.b": []}, [])
        with patch("tools.rocq_readable.explanations.shutil.which", return_value="codex"), \
             patch("tools.rocq_readable.explanations.query", side_effect=StartupBlocked("Sandbox startup blocked.")) as model:
            result = explain(self.sources, self.documents, self.graph, Options("auto"))
        self.assertEqual(model.call_count, 1)
        self.assertTrue(all(item["status"] == "failed" for item in result.values()))

    def test_generation_failure_still_writes_pages_and_reports(self):
        output = self.root / "html"
        with patch("tools.rocq_readable.explanations.shutil.which", return_value="codex"), \
             patch("tools.rocq_readable.explanations.query", side_effect=ValueError("SECRET")):
            result = generate(self.sources, {}, Dictionary(DEFAULT_DICTIONARY), output, explanation_options=Options("auto"))
        self.assertEqual(result.explanation_failures, 1)
        report = json.loads((output / "report.json").read_text())
        self.assertFalse(report["dependencies"]["complete"])
        self.assertEqual(report["explanations"]["failures"], 1)
        self.assertNotIn("SECRET", (output / "report.json").read_text())
        self.assertIn("Explanation unavailable", (output / "A.html").read_text())
        self.assertIn("<h1>Index</h1>", (output / "declarations.html").read_text())
        audit_links(output)

    def test_cached_generation_is_deterministic_and_escapes_explanations(self):
        output = self.root / "html"
        options = Options("auto", "model")
        with patch("tools.rocq_readable.explanations.shutil.which", return_value="codex"), \
             patch("tools.rocq_readable.explanations.query", return_value="<script>alert('x')</script> & text") as model:
            generate(self.sources, {}, Dictionary(DEFAULT_DICTIONARY), output, explanation_options=options)
            first = {p.name: p.read_bytes() for p in output.iterdir()}
            generate(self.sources, {}, Dictionary(DEFAULT_DICTIONARY), output, explanation_options=options)
            self.assertEqual(first, {p.name: p.read_bytes() for p in output.iterdir()})
            self.assertEqual(model.call_count, 1)
        self.assertIn("&lt;script&gt;", (output / "A.html").read_text())
        audit_links(output)

    def test_cli_returns_failure_after_rendering_failed_explanations(self):
        self.source.path.write_text(self.source.text)
        previous = Path.cwd()
        try:
            os.chdir(self.root)
            with patch("tools.rocq_readable.cli.prepare", return_value=(self.sources, {})), \
                 patch("tools.rocq_readable.explanations.shutil.which", return_value="codex"), \
                 patch("tools.rocq_readable.explanations.query", side_effect=ValueError("SECRET")), \
                 redirect_stderr(io.StringIO()), redirect_stdout(io.StringIO()):
                self.assertEqual(main(["build", "--output", "html"]), 1)
            self.assertTrue((self.root / "html/index.html").is_file())
            self.assertEqual(json.loads((self.root / "html/report.json").read_text())["explanations"]["failures"], 1)
        finally:
            os.chdir(previous)

    def test_standalone_explanation_preserves_other_artifacts(self):
        output = self.root / "html"
        output.mkdir()
        for name in ("index.html", "declarations.html", "style.css", "explanations.json"):
            (output / name).write_text("existing content")
        target = output / "a.html"
        with patch("tools.rocq_readable.explanations.shutil.which", return_value="codex"), \
             patch("tools.rocq_readable.explanations.query", return_value="Defines zero."):
            generate(self.sources, {}, Dictionary(DEFAULT_DICTIONARY), output, single=target, explanation_options=Options("auto"))
        for name in ("index.html", "declarations.html", "style.css", "explanations.json"):
            self.assertEqual((output / name).read_text(), "existing content")
        self.assertIn("Defines zero.", target.read_text())
        self.assertTrue(target.with_suffix(".explanations.json").is_file())
        self.assertNotIn('href="declarations.html"', target.read_text())

    def test_reserved_source_filenames_do_not_overwrite_navigation(self):
        self.source.path = self.root / "index.v"
        output = self.root / "html"
        generate(self.sources, {}, Dictionary(DEFAULT_DICTIONARY), output)
        self.assertTrue((output / "index.source.html").is_file())
        self.assertIn("Dependency hierarchy", (output / "index.html").read_text())
        audit_links(output)

    def test_generated_schemes_preserve_inductive_identity(self):
        path = self.root / "A.v"
        data = b"Inductive color := Red.\n"
        path.with_suffix(".glob").write_text("DIGEST " + hashlib.md5(data).hexdigest() + "\nFP.A\nind 10:14 <> color\nconstr 19:21 <> Red\nscheme 10:14 <> color_ind\nscheme 10:14 <> color_sind\n")
        self.assertEqual(Glob.load(path, data).definitions[10], ("P.A.color", "ind"))


@unittest.skipUnless(backend_available(), "install the pinned coq-lsp backend for integration tests")
class RocqIntegration(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.root = Path(cls.temporary.name).resolve()
        (cls.root / "_CoqProject").write_text("-Q . readable_test\n")
        (cls.root / "A.v").write_text('''From Coq Require Import List Arith.
Import ListNotations.
Module Inner.
Definition value : nat := 1.
End Inner.
Definition value : nat := 2.
Definition id (x : nat) : nat := x.
Fixpoint count (xs : list nat) : nat := match xs with [] => 0 | x :: rest => S (count rest) end.
Inductive color := Red | Blue.
Record box := Box { item : nat; flag : bool }.
Section Example.
Context {A : Type}.
Definition shadow (value : nat) : nat := value.
Definition lambda_shadow (x : nat) := fun x : nat => x.
Lemma law (x : nat) : forall y : nat, x = y -> id x = y.
Proof. intros y H. exact H. Qed.
Lemma based_on_law (x : nat) : id x = x.
Proof. apply law. reflexivity. Qed.
End Example.
''')
        (cls.root / "B.v").write_text('''From readable_test Require Import A.
Definition use := A.id A.value.
Definition inner := A.Inner.value.
Definition red := A.Red.
Definition field (b : A.box) := A.item b.
''')
        binary = Path(executable()).with_name("coqc")
        for name in ("A", "B"):
            subprocess.run([str(binary), "-Q", ".", "readable_test", name + ".v"], cwd=cls.root,
                           check=True, capture_output=True, timeout=60)
        with redirect_stderr(io.StringIO()):
            cls.sources, cls.resolutions = prepare([cls.root / "A.v", cls.root / "B.v"], cls.root, 30)
        errors = [e for source in cls.sources for e in source.errors]
        if errors:
            raise AssertionError(errors)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def test_whole_project_links_shadowing_types_and_no_proofs(self):
        output = self.root / "html"
        dictionary = Dictionary(DEFAULT_DICTIONARY)
        dictionary.replace({"kind": "application", "key": "readable_test.A.id", "arity": 1,
                            "label": "identity", "slots": [0]})
        generate(self.sources, self.resolutions, dictionary, output)
        audit_links(output)
        a, b = (output / "A.html").read_text(), (output / "B.html").read_text()
        self.assertNotIn("Proof.", a)
        self.assertNotIn("intros y", a)
        self.assertNotIn("Qed.", a)
        self.assertIn('A.html#' + anchor("readable_test.A.id"), b)
        self.assertIn('A.html#' + anchor("readable_test.A.Red"), b)
        self.assertIn('A.html#' + anchor("readable_test.A.item"), b)
        self.assertIn('>identity</a>', b)
        self.assertNotIn('href="http', a + b)
        self.assertIn('href="#' + anchor("readable_test.A.shadow") + '-binder-', a)
        first = {str(p.relative_to(output)): p.read_bytes() for p in output.rglob("*") if p.is_file()}
        generate(self.sources, self.resolutions, dictionary, output)
        self.assertEqual(first, {str(p.relative_to(output)): p.read_bytes() for p in output.rglob("*") if p.is_file()})

    def test_proof_dependencies_links_and_local_shadowing(self):
        output = self.root / "dependencies-html"
        generate(self.sources, self.resolutions, Dictionary(DEFAULT_DICTIONARY), output)
        graph = json.loads((output / "report.json").read_text())["dependencies"]["declarations"]
        self.assertIn("readable_test.A.law", graph["readable_test.A.based_on_law"]["depends_on"])
        self.assertNotIn("readable_test.A.value", graph["readable_test.A.shadow"]["depends_on"])
        self.assertEqual(graph["readable_test.B.red"]["depends_on"], ["readable_test.A.color"])
        self.assertEqual(graph["readable_test.B.field"]["depends_on"], ["readable_test.A.box"])
        self.assertIn("readable_test.A.count", graph["readable_test.A.count"]["depends_on"])
        inventory = (output / "declarations.html").read_text()
        for source in self.sources:
            for decl in source.declarations:
                self.assertIn(anchor(decl.identity), inventory)
        homepage = (output / "index.html").read_text()
        self.assertIn('type="application/json"', homepage)
        self.assertIn('class="dependency-tree"', homepage)
        self.assertNotIn("Proof.", (output / "A.html").read_text())
        audit_links(output)

    def test_lsp_resolves_proof_references_without_glob(self):
        path = self.root / "ProofDeps.v"
        path.write_text('Definition n := 0.\nLemma first : n = 0. Proof. reflexivity. Qed.\nLemma second : n = 0. Proof. exact first. Qed.\nDefinition shadow (n : nat) := n.\nLemma H : True. Proof. exact I. Qed.\nLemma local_proof : True -> True. Proof. intros H. exact H. Qed.\nLemma local_parameter (H : True) : True. Proof. exact H. Qed.\n')
        with redirect_stderr(io.StringIO()):
            sources, resolutions = prepare([path], self.root, 30)
        output = self.root / "fallback-html"
        generate(sources, resolutions, Dictionary(DEFAULT_DICTIONARY), output)
        graph = json.loads((output / "report.json").read_text())["dependencies"]
        self.assertIn("readable_test.ProofDeps.first", graph["declarations"]["readable_test.ProofDeps.second"]["depends_on"])
        self.assertNotIn("readable_test.ProofDeps.n", graph["declarations"]["readable_test.ProofDeps.shadow"]["depends_on"])
        for name in ("local_proof", "local_parameter"):
            self.assertNotIn("readable_test.ProofDeps.H", graph["declarations"]["readable_test.ProofDeps." + name]["depends_on"])
        self.assertFalse(graph["complete"])
        audit_links(output)

    def test_selected_statement_does_not_require_proof(self):
        path = self.root / "Unfinished.v"
        path.write_text("(* A leading comment: Σ *)\nDefinition id (x : nat) := x.\nLemma unfinished : id 0 = 0.\nProof. THIS_IS_NOT_A_TACTIC.\n")
        with redirect_stderr(io.StringIO()):
            sources, resolutions = prepare([path], self.root, 30, selected="unfinished")
        self.assertEqual(sources[0].errors, [])
        self.assertEqual(sources[0].declarations[-1].name, "unfinished")
        self.assertNotIn("THIS_IS_NOT_A_TACTIC", sources[0].declarations[-1].source)
        sources[0].declarations = [sources[0].declarations[-1]]
        output = self.root / "selected.html"
        generate(sources, resolutions, Dictionary(DEFAULT_DICTIONARY), self.root, single=output)
        report = json.loads(output.with_suffix(".report.json").read_text())
        self.assertTrue(any("Proof dependency coverage" in issue for issue in report["dependencies"]["declarations"]["readable_test.Unfinished.unfinished"]["issues"]))

    def test_selected_source_build_omits_unrelated_scratch_file(self):
        scratch = self.root / "Scratch.v"
        scratch.write_text("This is an incomplete proof fragment.\n")
        previous = Path.cwd()
        try:
            os.chdir(self.root)
            with redirect_stderr(io.StringIO()), redirect_stdout(io.StringIO()):
                status = main(["build", "--sources", "A.v", "B.v", "--output", "selected-html",
                               "--explanations", "offline"])
            self.assertEqual(status, 0)
            report = json.loads((self.root / "selected-html/report.json").read_text())
            self.assertEqual({f["file"] for f in report["files"]}, {"A.v", "B.v"})
            self.assertFalse((self.root / "selected-html/Scratch.html").exists())
            audit_links(self.root / "selected-html")
        finally:
            os.chdir(previous)
            scratch.unlink()
    def test_single_cli_strict_unknown_rules_and_ambiguous_names(self):
        rules = self.root / "empty-rules.json"
        rules.write_text('{"version":1,"rules":[]}')
        output = self.root / "standalone"
        output.mkdir(exist_ok=True)
        (output / "index.html").write_text("existing index")
        (output / "style.css").write_text("existing style")
        previous = Path.cwd()
        try:
            os.chdir(self.root)
            with redirect_stderr(io.StringIO()), redirect_stdout(io.StringIO()):
                status = main(["render", "A.v", "--name", "law", "--output", "standalone/law.html",
                               "--dictionary", str(rules), "--strict", "--explanations", "offline"])
                ambiguous = main(["render", "A.v", "--name", "value", "--output", "standalone/ambiguous.html", "--explanations", "offline"])
            self.assertEqual(status, 1)
            self.assertEqual(ambiguous, 1)
            self.assertFalse((output / "ambiguous.html").exists())
            self.assertEqual((output / "index.html").read_text(), "existing index")
            self.assertEqual((output / "style.css").read_text(), "existing style")
            page = (output / "law.html").read_text()
            self.assertNotIn("Proof.", page)
            self.assertNotIn('href="index.html"', page)
            self.assertIn("unsupported or unmapped constructs", page)
            self.assertIn("notation &quot;_", page)
            self.assertTrue(json.loads((output / "law.report.json").read_text())["files"][0]["unsupported"])
            audit_links(output)
        finally:
            os.chdir(previous)

    def test_bad_file_does_not_prevent_other_pages_and_returns_failure(self):
        (self.root / "Broken.v").write_text("Definition broken : nat := missing_symbol.\n")
        (self.root / "Malformed.v").write_bytes(b"Definition malformed := \xff.\n")
        previous = Path.cwd()
        try:
            os.chdir(self.root)
            with redirect_stderr(io.StringIO()), redirect_stdout(io.StringIO()):
                status = main(["build", "--output", "partial-html", "--explanations", "offline"])
            self.assertEqual(status, 1)
            self.assertTrue((self.root / "partial-html/A.html").exists())
            report = json.loads((self.root / "partial-html/report.json").read_text())
            self.assertTrue(next(f for f in report["files"] if f["file"] == "Malformed.v")["errors"])
            audit_links(self.root / "partial-html")
        finally:
            os.chdir(previous)
            (self.root / "Broken.v").unlink()
            (self.root / "Malformed.v").unlink()
            (self.root / "Unfinished.v").unlink(missing_ok=True)

    def test_cjr_contracts_and_definition_vocabulary(self):
        dictionary = Dictionary(DEFAULT_DICTIONARY)
        models = []
        for file, selected, expected in [("swap", "swap_wp", "consuming_implies"),
                                          ("list", "is_list", "exists"),
                                          ("array", "array_cells", "separately_for_each_index_and_item"),
                                          ("most_frequent", "most_frequent_spec", "forall")]:
            group = "misc" if file == "swap" else file
            path = ROOT / f"example/{group}/rocq/{file}.v"
            with redirect_stderr(io.StringIO()):
                sources, resolutions = prepare([path], ROOT, 60, selected=selected)
            self.assertEqual(sources[0].errors, [], file)
            models.extend(sources)
            declaration = next(d for d in sources[0].declarations if d.name == selected)
            adapter = Adapter(sources[0], dictionary, {d.identity for d in sources[0].declarations})
            document = adapter.declaration(declaration)
            self.assertIn(expected, document.plain())
            self.assertNotIn("Proof.", declaration.source)
        output = self.root / "cjr-html"
        generate(models, {}, dictionary, output)
        audit_links(output)


class CustomSyntaxTests(unittest.TestCase):
    def test_templates_validate_reload_and_preserve_links(self):
        from tools.rocq_readable.layout import render_html
        base = {"kind": "application", "key": "P.eq", "arity": 2, "label": "equals", "template": "{0}={1}"}
        for text in ("{0}", "{0}={0}", "{0}={2}", "{x}={1}", "{0!r}={1}", "{0:04}={1}", "{0}={1", "{0.__class__}={1}", " {0}\n{1}"):
            with self.subTest(text=text), self.assertRaises(DictionaryError):
                validate({**base, "template": text})
        with tempfile.TemporaryDirectory() as tmp:
            dictionary = Dictionary(Path(tmp) / "rules.json")
            dictionary.replace(base)
            dictionary.save()
            dictionary = Dictionary(dictionary.path)
            doc = dictionary.apply(dictionary.rules[0], Token("eq", identity="P.eq"), [leaf("A", local="binder-A"), leaf("<B>", identity="P.B")])
            self.assertEqual(doc.plain(), "A=<B>")
            target = Path(tmp) / "out.html"
            rendered = render_html(doc, target, {"P.eq": (target, "eq"), "P.B": (target, "B")})
            self.assertIn('href="#binder-A"', rendered)
            self.assertIn('href="#eq"', rendered)
            self.assertIn('&lt;B&gt;', rendered)
            self.assertIn('href="#B"', rendered)

    def test_nested_and_multiline_templates(self):
        equal = Doc(Token("equals"), [leaf("A"), leaf("B")], template="{0}={1}")
        implies = Doc(Token("arrow"), [equal, leaf("C")], template="IF {0} THEN {1}")
        self.assertEqual(implies.plain(), "IF (A=B) THEN C")
        self.assertEqual(Doc(Token("f"), [implies]).plain(), "f(IF (A=B) THEN C)")
        loop = Doc(Token("while"), [leaf("ready"), Doc(Token("seq"), [leaf("first()"), leaf("second()")], template="{0}\n{1}")], template="while ({0}) {{\n    {1}\n}}")
        self.assertEqual(loop.plain(), "while (ready) {\n    first()\n    second()\n}")
        long = Doc(Token("eq"), [leaf("A" * 80), leaf("B" * 80)], template="{0}={1}")
        self.assertEqual(long.plain().count("A"), 80)
        self.assertEqual(long.plain().count("B"), 80)
        self.assertIn("=", long.plain())
        forced = Doc(Token("eq"), [leaf("A"), leaf("B")], block=True, template="{0}={1}")
        self.assertEqual(forced.plain(), "    A\n=\n    B")
        transparent = Doc(Token("wrapper"), [equal], template="{0}")
        self.assertEqual(transparent.plain(), "A=B")
        self.assertEqual(Doc(Token("op"), [transparent, leaf("C")], template="{0}+{1}").plain(), "(A=B)+C")
        nested_long = Doc(Token("arrow"), [long, leaf("C")], template="IF {0} THEN {1}")
        multiline = nested_long.plain()
        self.assertEqual(multiline.count("("), 1)
        self.assertEqual(multiline.count(")"), 1)
        self.assertLess(multiline.index(")"), multiline.index("THEN"))

    def test_learning_accepts_custom_template(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            dictionary = Dictionary(root / "rules.json")
            encounters = {("application", "P.eq", 2, None, None): (Token("eq"), [leaf("A"), leaf("B")], "eq A B")}
            with patch("builtins.input", side_effect=["1", '{"label":"equals","template":"{0}={1}"}', "y", "done"]), redirect_stdout(io.StringIO()):
                learning(dictionary, encounters, root / "preview")
            self.assertEqual(Dictionary(dictionary.path).rules[0]["template"], "{0}={1}")
            self.assertIn("A=B", (root / "preview/rule-preview.html").read_text())


@unittest.skipUnless(backend_available(), "install the pinned coq-lsp backend for integration tests")
class CustomSyntaxIntegration(unittest.TestCase):
    def test_sorts_cangjie_and_original_source(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            path = root / "Syntax.v"
            config = f'-Q . SyntaxTest\n-Q {ROOT / "theories"} cjr\n'
            (root / "_CoqProject").write_text(config)
            path.write_text('''From Coq Require Import String ZArith.
From cjr Require Import notation.
Open Scope string_scope.
Open Scope Z_scope.
Definition implication (P Q : Prop) : Prop := P -> Q.
Definition function_type := Z -> Z.
Definition mixed (P : Prop) : Prop := (Z -> Z) = (Z -> Z) -> P.
Definition nested := forall (P Q : Prop), P -> Q.
Definition program : expr := VarBind "x" (Val (LitV (LitInt 1)))
  (While (BinOp LeOp (Var "x") (Val (LitV (LitInt 4))))
    (Assign "x" (BinOp PlusOp (Var "x") (Val (LitV (LitInt 1)))))).
Definition lambda_code : expr := Rec None (Some "x") (Var "x").
Definition pointer_code (p : expr) : expr := Store p (Load p).
Definition anonymous_let : expr := Let None (Val (LitV LitUnit)) (Val (LitV LitUnit)).
Definition symbolic_name (name : string) : expr := Var name.
Definition stack_code (p : expr) : expr := StackLoad p.
Definition sum_code (a b : expr) : expr := (a + b)%E.
Definition product_code (a b : expr) : expr := (a * b)%E.
Definition product_ast (a b : expr) : expr := BinOp MulOp a b.
Definition call_code (f x : expr) : expr := App f x.
Definition branch_code (b : bool) : expr := If (Val (LitV (LitBool b))) (Val (LitV LitNull)) (Val (LitV (LitFloat 2))).
Definition allocation (n : expr) : expr := Seq (Free (Alloc n)) (Offset n n).
''')
            binary = Path(executable()).with_name("coqc")
            subprocess.run([str(binary), "-Q", ".", "SyntaxTest", "-Q", str(ROOT / "theories"), "cjr", str(path)], cwd=root, check=True, capture_output=True, timeout=60)
            with redirect_stderr(io.StringIO()):
                sources, resolutions = prepare([path], root, 30)
            source = sources[0]
            self.assertEqual(source.errors, [])
            adapter = Adapter(source, Dictionary(DEFAULT_DICTIONARY), {d.identity for d in source.declarations})
            docs = {d.name: adapter.declaration(d).plain() for d in source.declarations}
            self.assertIn("IF P THEN Q", docs["implication"])
            self.assertIn("arrow(Z, Z)", docs["function_type"])
            self.assertIn("IF (arrow(Z, Z)=arrow(Z, Z)) THEN P", docs["mixed"])
            self.assertIn("IF P THEN Q", docs["nested"])
            self.assertIn("var x = 1", docs["program"])
            self.assertIn("while (", docs["program"])
            self.assertIn("x = (x + 1)", docs["program"])
            self.assertIn("{ x =>", docs["lambda_code"])
            self.assertIn(".write(", docs["pointer_code"])
            self.assertIn(".read()", docs["pointer_code"])
            self.assertIn("let _ = ()", docs["anonymous_let"])
            self.assertIn("CJR Var [symbolic identifier or binder](name)", docs["symbolic_name"])
            self.assertIn("CJR StackLoad", docs["stack_code"])
            self.assertIn("a + b", docs["sum_code"])
            self.assertIn("a * b", docs["product_code"])
            self.assertIn("a * b", docs["product_ast"])
            self.assertIn("f(x)", docs["call_code"])
            self.assertIn("CPointer<Int64>()", docs["branch_code"])
            self.assertIn("2.0", docs["branch_code"])
            self.assertIn("calloc", docs["allocation"])
            output = root / "html"
            generate(sources, resolutions, Dictionary(DEFAULT_DICTIONARY), output)
            html = (output / "Syntax.html").read_text()
            self.assertIn("Original declaration", html)
            self.assertIn("VarBind", html)
            self.assertIn("cangjie-binder", html)
            audit_links(output)
            source.arrow_sorts.clear()
            adapter = Adapter(source, Dictionary(DEFAULT_DICTIONARY), set())
            adapter.declaration(next(d for d in source.declarations if d.name == "implication"))
            self.assertTrue(any("unclassified arrow" in item for item in adapter.coverage))


if __name__ == "__main__":
    unittest.main()
