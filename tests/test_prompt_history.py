"""Git fixture tests: attribution, cache lifecycle, and explanation preservation."""
from __future__ import annotations

import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from tools.rocq_readable.ast import Declaration
from tools.rocq_readable.history import (added_records, backwards, collect, extract_commit, git,
                                        panel, patch_hunks, records)
from tools.rocq_readable.html import page
from tools.rocq_readable.layout import leaf
from tools.rocq_readable.project import Glob, Source
from tools.rocq_readable.refresh_history import SavedPage, proof_end, refresh


A = "Definition a := 1.\n"
B = "Lemma b : True.\nProof.\n  exact I.\nQed.\n"


class GitHistoryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / "repo"
        self.root.mkdir()
        self.init(self.root)
        (self.root / "logs").mkdir()
        (self.root / "logs/prompts.txt").write_text("")
        (self.root / "test.v").write_text(A + B)
        self.initial = self.commit("initial", ["Create both declarations"])

    def init(self, root):
        git(root, "init", "-b", "main")
        git(root, "config", "user.name", "Fixture")
        git(root, "config", "user.email", "fixture@example.test")

    def commit(self, subject, prompts=(), root=None):
        root = root or self.root
        log = root / "logs/prompts.txt"
        for prompt in prompts:
            with log.open("a") as stream:
                stream.write("[2026-10-10T10:00:00+00:00]\n" + prompt + "\n\n")
        git(root, "add", ".")
        git(root, "commit", "-m", subject)
        return git(root, "rev-parse", "HEAD").strip()

    def source(self, path="test.v", root=None):
        root = root or self.root
        text = (root / path).read_text()
        source = Source(root / path, root, text, "Test", Glob())
        for name, snippet in (("a", A.strip()), ("b", B.splitlines()[0])):
            # Tests may change a's value or b's proof, retaining their names.
            start = text.index("Definition a" if name == "a" else "Lemma b")
            stop = text.index("\n", start)
            decl = Declaration(name, "Test." + name, "definition", {}, text[start:stop],
                               source_start=len(text[:start].encode()))
            if name == "b":
                ep = text.index("Qed.", start) + 4
                decl.proof_spans = [{"loc": {"ep": len(text[:ep].encode())}}]
            source.declarations.append(decl)
        return source

    def test_records_keep_multiline_and_literal_content(self):
        text = '[2026-10-10T10:00:00+00:00]\n<script>\n$(literal)\n\n\n'
        self.assertEqual(records(text)[0]["text"], "<script>\n$(literal)\n")
        self.assertEqual(added_records(text, text), [])
        self.assertEqual(len(added_records(text, text + text)), 1)

    def test_definition_and_proof_edits_include_all_new_prompts(self):
        (self.root / "test.v").write_text(A + B.replace("exact I", "now exact I"))
        changed = self.commit("proof change", ["Improve proof", "<b>second prompt</b>\nwith details"])
        result = collect([self.source()])
        self.assertEqual([e["commit"] for e in result["Test.a"]["entries"]], [self.initial])
        self.assertEqual([e["commit"] for e in result["Test.b"]["entries"]], [changed, self.initial])
        self.assertEqual(len(result["Test.b"]["entries"][0]["prompts"]), 2)
        markup = panel(result["Test.b"])
        self.assertIn("&lt;b&gt;second prompt&lt;/b&gt;", markup)
        self.assertNotIn("<script>", markup)
        self.assertTrue(markup.startswith('<details class="prompt-history">'))
        self.assertEqual(markup.count('<details class="history-prompt-disclosure">'), 3)
        self.assertIn('<summary>Prompt 2 · 2026-10-10T10:00:00+00:00</summary>', markup)
        self.assertNotIn(" open", markup)

    def test_edits_without_prompts_still_shift_earlier_ranges(self):
        (self.root / "test.v").write_text("(* header *)\n\n" + A + B)
        self.commit("shift only")
        result = collect([self.source()])
        self.assertEqual([e["commit"] for e in result["Test.b"]["entries"]], [self.initial])

    def test_rename_tracks_original_path(self):
        git(self.root, "mv", "test.v", "renamed.v")
        self.commit("rename", ["Move file"])
        result = collect([self.source("renamed.v")])
        self.assertEqual([e["commit"] for e in result["Test.b"]["entries"]], [self.initial])

    def test_new_definition_does_not_inherit_neighbour_history(self):
        (self.root / "test.v").write_text(A + "Definition fresh := 3.\n" + B)
        created = self.commit("new definition", ["Add fresh"])
        source = self.source()
        text = "Definition fresh := 3."
        source.declarations = [Declaration("fresh", "Test.fresh", "definition", {}, text,
                                          source_start=len(A.encode()))]
        result = collect([source])["Test.fresh"]
        self.assertEqual([e["commit"] for e in result["entries"]], [created])

    def test_cache_reuse_incremental_updates_and_rewrite(self):
        source = self.source()
        first = collect([source])
        cache = self.root / "build/prompt-history.json"
        original = cache.read_bytes()
        with patch("tools.rocq_readable.history.extract_commit", side_effect=AssertionError("re-extracted")):
            self.assertEqual(collect([source]), first)
        self.assertEqual(cache.read_bytes(), original)
        # Do not accidentally commit the generated cache in this fixture.
        (self.root / ".gitignore").write_text("build/\n")
        (self.root / "test.v").write_text(A.replace("1", "2") + B)
        new = self.commit("change a", ["Change a"])
        with patch("tools.rocq_readable.history.extract_commit", wraps=extract_commit) as extract:
            collect([self.source()])
        self.assertEqual([call.args[1] for call in extract.call_args_list], [new])
        git(self.root, "reset", "--hard", self.initial)
        result = collect([self.source()])
        self.assertNotIn(new, [e["commit"] for e in result["Test.a"]["entries"]])

    def test_corrupt_cache_recovers_and_no_git_uses_cached_entries(self):
        cache = self.root / "build/prompt-history.json"
        cache.parent.mkdir()
        cache.write_text('{"version":1,"associations":{},"primary":{"bad":true}}')
        expected = collect([self.source()])
        with patch("tools.rocq_readable.history.git", side_effect=FileNotFoundError()):
            actual = collect([self.source()])
        self.assertEqual(actual["Test.a"]["entries"], expected["Test.a"]["entries"])
        self.assertFalse(actual["Test.a"]["complete"])

    def test_shallow_checkout_can_be_deepened_without_head_change(self):
        (self.root / "test.v").write_text(A + B.replace("exact I", "now exact I"))
        self.commit("latest proof", ["Latest prompt"])
        clone = Path(self.tmp.name) / "shallow"
        git(Path(self.tmp.name), "clone", "--depth=1", self.root.resolve().as_uri(), str(clone))
        shallow = collect([self.source(root=clone)])["Test.a"]
        self.assertFalse(shallow["complete"])
        self.assertNotIn(self.initial, [e["commit"] for e in shallow["entries"]])
        git(clone, "fetch", "--unshallow")
        full = collect([self.source(root=clone)])["Test.a"]
        self.assertTrue(full["complete"])
        self.assertEqual([e["commit"] for e in full["entries"]], [self.initial])

    def test_custom_named_explanation_cache_is_protected(self):
        cache = self.root / "custom-cache.json"
        text = '{"version":1,"entries":{"explanation":"keep me"}}'
        cache.write_text(text)
        with self.assertRaises(ValueError):
            collect([self.source()], cache=cache)
        self.assertEqual(cache.read_text(), text)

    def test_example_builds_share_repository_cache(self):
        source = self.source()
        collect([source])
        example = self.root / "example"
        example.mkdir()
        git(self.root, "mv", "test.v", "example/test.v")
        self.commit("move into example")
        nested = self.source("example/test.v")
        nested.root = example
        result = collect([nested])
        self.assertTrue(result["Test.a"]["entries"])
        self.assertTrue((self.root / "build/prompt-history.json").is_file())
        self.assertFalse((example / "build/prompt-history.json").exists())

    def test_single_definition_html_preserves_explanation_and_embeds_history(self):
        source = self.source()
        source.declarations = source.declarations[:1]
        result = collect([source])
        target = self.root / "single.html"
        markup = page(source, [leaf("a")], target, self.root, {}, [], standalone=True,
                      explanations={"Test.a": {"description": "Preserved AI explanation"}}, history=result)
        self.assertIn("Preserved AI explanation", markup)
        self.assertIn("Create both declarations", markup)
        self.assertNotIn("<details open", markup)
        self.assertIn("<style>", markup)
        target.write_text(markup)
        report = {"explanations": {"keep": "Preserved AI explanation"}}
        target.with_suffix(".report.json").write_text(json.dumps(report))
        refresh(self.root, target)
        self.assertEqual(target.read_text(), markup)
        self.assertEqual(json.loads(target.with_suffix(".report.json").read_text())["explanations"], report["explanations"])

    def test_dirty_source_shifts_and_uncommitted_prompts_are_ignored(self):
        (self.root / "test.v").write_text("(* uncommitted header *)\n" + A + B)
        with (self.root / "logs/prompts.txt").open("a") as stream:
            stream.write("[2026-10-11T10:00:00+00:00]\nNOT COMMITTED\n\n")
        result = collect([self.source()])
        self.assertNotIn("NOT COMMITTED", json.dumps(result))
        self.assertEqual(result["Test.a"]["entries"][0]["commit"], self.initial)

    def test_first_parent_merge_attributes_prompts_once(self):
        git(self.root, "checkout", "-b", "feature")
        (self.root / "test.v").write_text(A.replace("1", "2") + B)
        self.commit("branch change", ["Branch prompt"])
        git(self.root, "checkout", "main")
        git(self.root, "merge", "--no-ff", "feature", "-m", "merge feature")
        result = collect([self.source()])["Test.a"]
        prompts = [p["text"] for e in result["entries"] for p in e["prompts"]]
        self.assertEqual(prompts.count("Branch prompt"), 1)
        self.assertEqual(result["entries"][0]["subject"], "merge feature")

    def test_migration_bridge_and_standalone_child(self):
        child = Path(self.tmp.name) / "child"
        child.mkdir()
        self.init(child)
        (child / "logs").mkdir()
        shutil.copyfile(self.root / "logs/prompts.txt", child / "logs/prompts.txt")
        shutil.copyfile(self.root / "test.v", child / "test.v")
        (child / "repository.json").write_text(json.dumps({"checkpoint": self.initial}))
        self.commit("split baseline", root=child)
        (self.root / "migration-manifest.json").write_text(json.dumps({"checkpoint": self.initial, "files": [
            {"source": "test.v", "destinations": ["child/test.v"]}]}))
        result = collect([self.source(root=child)], history_repository=self.root)
        self.assertEqual([e["commit"] for e in result["Test.a"]["entries"]], [self.initial])
        self.assertTrue(result["Test.a"]["complete"])
        shutil.rmtree(self.root / ".git")
        with patch("tools.rocq_readable.history.extract_commit", side_effect=AssertionError("re-extracted")):
            cached = collect([self.source(root=child)])
        self.assertEqual(result, cached)
        cache = json.loads((child / "build/prompt-history.json").read_text())
        self.assertEqual(cache["primary"]["commits"][0]["prompts"], [])

    def test_refresh_preserves_all_existing_content_and_explanations(self):
        source = self.source()
        out = self.root / "docs"
        out.mkdir()
        report = {"files": [{"file": "test.v"}], "explanations": {"declarations": {
            "Test.a": {"description": "KEEP THIS EXPLANATION"}}}, "other": {"keep": True}}
        (out / "report.json").write_text(json.dumps(report))
        explanation_cache = out / "explanations.json"
        explanation_cache.write_text('{"version":1,"entries":{"keep":"exactly"}}')
        before_cache = explanation_cache.read_bytes()
        target = out / "test.html"
        original = page(source, [leaf("a"), leaf("b")], target, out, {}, [],
                        explanations={"Test.a": {"description": "KEEP THIS EXPLANATION"}})
        # Emulate an older page, before history panels existed.
        saved = SavedPage(original)
        for article in reversed(saved.articles):
            start, end = article["history"]
            original = original[:start] + original[end:]
        target.write_text(original)
        result = refresh(self.root, out)
        self.assertTrue(result["Test.b"]["entries"])
        after = target.read_text()
        parsed = SavedPage(after)
        self.assertEqual(len(parsed.articles), 2)
        for article in reversed(parsed.articles):
            start, end = article["history"]
            after = after[:start] + after[end:]
        self.assertEqual(after, original)
        self.assertEqual(explanation_cache.read_bytes(), before_cache)
        updated = json.loads((out / "report.json").read_text())
        self.assertEqual(updated["explanations"], report["explanations"])
        self.assertEqual(updated["other"], report["other"])
        first = target.read_bytes()
        refresh(self.root, out)
        self.assertEqual(target.read_bytes(), first)
        with self.assertRaises(ValueError):
            refresh(self.root, out, cache=explanation_cache)
        self.assertEqual(explanation_cache.read_bytes(), before_cache)

    def test_proof_recovery_ignores_comment_and_string_terminators(self):
        text = 'Lemma b : True.\nProof. (* Qed. (* nested *) *)\n  let x := "Qed." in exact I.\nQed.\n'
        end, uncertain = proof_end(text, 0, len("Lemma b : True."), len(text))
        self.assertEqual(end, len(text.rstrip()))
        self.assertFalse(uncertain)

    def test_diff_boundaries_and_ambiguity(self):
        self.assertEqual(backwards([[4, 7]], [[1, 1, 1, 2]]), ([[3, 6]], False, False))
        self.assertEqual(backwards([[4, 7]], [[10, 1, 10, 2]]), ([[4, 7]], False, False))
        self.assertEqual(backwards([[4, 7]], [[3, 1, 3, 5]])[1:], (True, True))
        self.assertFalse(backwards([[4, 7]], [[7, 1, 7, 0]])[1])
        self.assertTrue(backwards([[4, 7]], [[5, 1, 5, 0]])[1])
        self.assertEqual(patch_hunks("@@ -0,0 +1,2 @@\n+x\n+y\n"), [[0, 0, 0, 2]])


if __name__ == "__main__":
    unittest.main()
