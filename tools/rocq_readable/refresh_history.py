"""Refresh history in saved HTML without rerendering existing explanations."""
from __future__ import annotations

from html.parser import HTMLParser
import json
from pathlib import Path
import re

from .ast import Declaration
from .history import collect, panel, repository
from .project import Glob, Source


def masked(text):
    """Hide nested Rocq comments and strings while preserving character offsets."""
    chars = list(text)
    depth, string, i = 0, False, 0
    while i < len(text):
        pair = text[i:i + 2]
        if not string and pair == "(*":
            depth += 1
            chars[i:i + 2] = "  "
            i += 2
            continue
        if depth and pair == "*)":
            depth -= 1
            chars[i:i + 2] = "  "
            i += 2
            continue
        if not depth and text[i] == '"':
            if string and pair == '""':
                chars[i:i + 2] = "  "
                i += 2
                continue
            string = not string
            chars[i] = " "
        elif (depth or string) and text[i] != "\n":
            chars[i] = " "
        i += 1
    return "".join(chars)


def proof_end(text, start, end, limit):
    """Recover only a clearly delimited proof for saved proof-free excerpts."""
    visible = masked(text)
    remainder = visible[end:limit]
    # A term-defined declaration cannot own the following proof block.
    header = visible[start:end]
    theorem = re.search(r"\b(?:Lemma|Theorem|Fact|Remark|Corollary|Proposition|Example|Goal)\b", header)
    definition = re.search(r"\b(?:Definition|Instance|Fixpoint)\b", header)
    needs_proof = bool(theorem or definition and ":=" not in header)
    if not needs_proof:
        return end, False
    close = re.search(r"\b(?:Qed|Defined|Admitted|Abort)\s*\.(?=\s|$)", remainder)
    return (end + close.end(), False) if close else (end, True)


class SavedPage(HTMLParser):
    def __init__(self, text):
        super().__init__(convert_charrefs=True)
        self.text = text
        self.lines = [0]
        for match in re.finditer("\n", text):
            self.lines.append(match.end())
        self.file, self.articles = "", []
        self.article = None
        self.capture = None
        self.summary, self.original = "", False
        self.details = []
        self.feed(text)

    def position(self):
        line, column = self.getpos()
        return self.lines[line - 1] + column

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == "h1":
            self.capture = "file"
        if tag == "article" and attrs.get("id", "").startswith("symbol-"):
            self.article = {"name": "", "identity": "", "source": "", "insert": None, "history": None}
        if not self.article:
            return
        if tag == "h2":
            self.capture = "name"
        if tag == "p" and attrs.get("class") == "meta" and not self.article["identity"]:
            self.capture = "identity"
        if tag == "details":
            history = "prompt-history" in attrs.get("class", "").split()
            self.details.append((self.position(), history))
        if tag == "summary":
            self.summary = ""
            self.capture = "summary"
        if tag == "pre" and self.original:
            self.capture = "source"

    def handle_data(self, data):
        if self.capture == "file":
            self.file += data
        elif self.capture == "summary":
            self.summary += data
        elif self.article and self.capture:
            self.article[self.capture] += data

    def handle_endtag(self, tag):
        if tag in ("h1", "h2", "p", "pre", "summary"):
            if tag == "summary":
                self.original = self.summary == "Original declaration (proof-free)"
            self.capture = None
        if tag == "details":
            self.original = False
            if self.details:
                start, history = self.details.pop()
                if history and self.article:
                    self.article["history"] = (start, self.position() + len("</details>"))
        if tag == "article" and self.article:
            self.article["insert"] = self.position()
            self.article["identity"] = self.article["identity"].split(" · ")[0]
            self.articles.append(self.article)
            self.article = None


def refresh(root, output, cache=None, history_repository=None):
    """Only replace History panels and report.history; other bytes stay intact."""
    root, output = Path(root).resolve(), Path(output).resolve()
    if not output.exists():
        raise ValueError("history refresh requires existing HTML output")
    standalone = output.is_file()
    if standalone and output.suffix != ".html":
        raise ValueError("single-page history refresh requires an .html file")
    report = output.with_suffix(".report.json") if standalone else output / "report.json"
    cache = Path(cache).resolve() if cache else repository(root) / "build/prompt-history.json"
    if cache.suffix != ".json" or cache.name.endswith("explanations.json") or cache == report:
        raise ValueError("history cache must be separate from explanations and reports")
    sources, pages, unavailable = [], [], {}
    for path in ([output] if standalone else sorted(output.rglob("*.html"))):
        text = path.read_text(encoding="utf-8")
        if "Original declaration (proof-free)" not in text:
            continue
        saved = SavedPage(text)
        source_path = (root / saved.file).resolve()
        if not source_path.is_relative_to(root) or not source_path.is_file():
            raise ValueError(f"saved page source is missing or outside project: {saved.file}")
        source = Source(source_path, root, source_path.read_text(encoding="utf-8"), "", Glob())
        located = []
        for article in saved.articles:
            excerpt = article["source"]
            matches = [m.start() for m in re.finditer(re.escape(excerpt), source.text)] if excerpt else []
            if len(matches) != 1:
                unavailable[article["identity"]] = {"entries": [], "complete": False,
                    "issues": ["Saved declaration cannot be located uniquely in the current source; rebuild its page."]}
                continue
            start = matches[0]
            decl = Declaration(article["name"], article["identity"], "", {}, excerpt,
                               source_start=len(source.text[:start].encode()))
            source.declarations.append(decl)
            located.append((start, decl))
        located.sort(key=lambda pair: pair[0])
        for i, (start, decl) in enumerate(located):
            limit = located[i + 1][0] if i + 1 < len(located) else len(source.text)
            end = start + len(decl.source)
            stop, uncertain = proof_end(source.text, start, end, limit)
            if uncertain:
                unavailable[decl.identity] = {"entries": [], "complete": False,
                    "issues": ["Saved page does not establish a complete proof range; rebuild its page."]}
            if stop > end:
                decl.proof_spans.append({"loc": {"ep": len(source.text[:stop].encode())}})
        sources.append(source)
        pages.append((path, text, saved))
    if not pages:
        raise ValueError("no saved declaration pages found in the requested output")
    history = collect(sources, cache, history_repository)
    history.update(unavailable)
    for path, text, saved in pages:
        edits = []
        for article in saved.articles:
            start, end = article["history"] or (article["insert"], article["insert"])
            edits.append((start, end, panel(history.get(article["identity"]))))
        for start, end, replacement in sorted(edits, reverse=True):
            text = text[:start] + replacement + text[end:]
        path.write_text(text, encoding="utf-8")
    if report.is_file():
        data = json.loads(report.read_text(encoding="utf-8"))
        data["history"] = {"complete": all(r["complete"] for r in history.values()), "declarations": history}
        report.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return history
