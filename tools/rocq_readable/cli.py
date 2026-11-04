"""CLI orchestration. Source and dictionaries are never changed by rendering."""
from __future__ import annotations

import argparse
from dataclasses import replace
import json
import math
from pathlib import Path
import sys
from urllib.parse import unquote, urlparse

from .ast import Adapter, declarations, value, walk
from .backend import Backend, BackendError
from .dictionary import Dictionary, DictionaryError
from .dependencies import build_graph, declaration_terms, reference_nodes
from .explanations import Options, explain
from .history import collect as collect_history, repository, validate_cache_path
from .html import CSS, index, inventory, page, shell
from .layout import anchor, render_html
from .project import Glob, Source, configuration, discover, inside


DEFAULT_DICTIONARY = Path(__file__).with_name("renderings.json")


def resolve_missing(backend, source):
    """Ask Rocq for destinations when no digest-verified .glob is available."""
    if source.glob.valid:
        return {}
    result = {}
    nodes = []
    for declaration in source.declarations:
        for term in declaration_terms(declaration):
            nodes.extend(reference_nodes(term))
    queried = set()
    for node in nodes:
        loc = node.get("loc")
        if not loc or loc["bp"] in queried:
            continue
        queried.add(loc["bp"])
        source.resolution_status[loc["bp"]] = "unresolved"
        prefix = source.text.encode()[:loc["bp"]].decode()
        lines = prefix.split("\n")
        position = {"line": len(lines) - 1, "character": len(lines[-1].encode("utf-16-le")) // 2}
        try:
            location = backend.request("textDocument/definition", {"textDocument": {"uri": source.path.as_uri()}, "position": position})
        except BackendError as exc:
            # An external library may have compiled objects but no navigable
            # source. That limits links, not the declaration's elaboration.
            if "library not found" in str(exc):
                continue
            raise
        if isinstance(location, list):
            location = location[0] if len(location) == 1 else None
        if location and "uri" in location:
            url = urlparse(location["uri"])
            target = Path(unquote(url.path)).resolve()
            if url.scheme == "file" and not url.netloc and inside(target, source.root):
                result[loc["bp"]] = (target, location["range"]["start"])
            else:
                source.resolution_status[loc["bp"]] = "external"
    return result


def prepare(paths, root, timeout, selected=None, term_view="elaborated"):
    plugin_path, plugin_error = None, None
    if term_view == "elaborated":
        from .plugin.build import build
        import subprocess
        try:
            plugin_path = build()
        except (OSError, RuntimeError, subprocess.SubprocessError) as exc:
            plugin_error = "Rocq term exporter unavailable: " + str(exc)
    sources, resolutions = [], {}
    from .gallina import fresh, render_compiled, render_source
    try:
        snapshots = [Source.load(path, root) for path in paths]
        compiled_view = bool(snapshots) and all(fresh(s) and s.glob.valid for s in snapshots)
    except (OSError, ValueError):
        compiled_view = False
    for path in paths:
        try:
            source = Source.load(path, root)
        except (OSError, ValueError) as exc:
            source = Source(path, root, "", ".".join(path.relative_to(root).with_suffix("").parts), Glob())
            source.errors.append(f"cannot load source/configuration: {exc}")
            sources.append(source)
            print(f"  error in {source.relative}: {exc}", file=sys.stderr)
            continue
        sources.append(source)
        print(f"Parsing {source.relative}", file=sys.stderr, flush=True)
        workspace = configuration(path, root).parent
        try:
            with Backend(workspace, timeout, plugin_path=plugin_path if not selected else None) as backend:
                document, diagnostics = backend.document(path, source.text, selected=selected, model=source)
                declarations(source, document)
                from .semantics import classify_arrows
                classify_arrows(backend, source)
                if term_view == "elaborated":
                    from .elaboration import export
                    if selected and plugin_path:
                        # The backend's synthetic startup Require has a ghost
                        # source range that interferes with ast_at_pos selection.
                        # Parse selection without it, then elaborate only the
                        # selected prefix in a separate initialized document.
                        stop = max(d.source_start + len(d.source.encode()) for d in source.declarations)
                        with Backend(workspace, timeout, plugin_path=plugin_path) as terms_backend:
                            terms_backend.document(path, source.text.encode()[:stop].decode(), model=source)
                            export(terms_backend, source)
                    else:
                        export(backend, source, plugin_error)
                # Prefer program-aware compiled printing when possible. An
                # empty environment can inline large shared helpers repeatedly
                # (notably AES substitution tables) before the contextual pass.
                if not compiled_view:
                    render_source(backend, source)
                errors = [d for d in diagnostics if d.get("severity") == 1]
                source.errors.extend(f"line {d['range']['start']['line'] + 1}: {d['message']}" for d in errors[:8])
                if len(errors) > 8:
                    source.errors.append(f"{len(errors) - 8} additional errors")
                if document.get("completed", {}).get("status") == ["Failed"] and not errors:
                    source.errors.append("Rocq could not finish parsing this source")
                resolutions[path] = resolve_missing(backend, source)
        except (BackendError, ValueError, KeyError, IndexError) as exc:
            source.errors.append(str(exc))
            print(f"  error: {exc}", file=sys.stderr)
    render_compiled(sources, timeout)
    return sources, resolutions


def identities(sources):
    return {decl.identity for source in sources for declaration in source.declarations
            for decl in (declaration, *declaration.children)}


def resolved_identities(resolutions, sources):
    result = {}
    by_path = {s.path: s for s in sources}
    for path, references in resolutions.items():
        result[path] = {}
        for offset, (target, position) in references.items():
            source = by_path.get(target)
            if not source:
                continue
            candidates = []
            lines = source.text.splitlines(keepends=True)
            line = lines[position["line"]] if position["line"] < len(lines) else ""
            prefix = line.encode("utf-16-le")[:2 * position["character"]].decode("utf-16-le")
            target_offset = len(("".join(lines[:position["line"]]) + prefix).encode())
            for declaration in source.declarations:
                for decl in (declaration, *declaration.children):
                    loc = decl.name_node.get("loc") or {}
                    if target_offset in (loc.get("bp"), decl.source_start):
                        candidates.append(decl.identity)
            # .glob-free LSP definitions return sentence starts. Never guess
            # when a line contains more than one destination.
            if len(candidates) == 1:
                result[path][offset] = candidates[0]
                by_path[path].resolution_status[offset] = "resolved"
            else:
                local_offsets = {n["loc"]["bp"] for d in source.declarations for n in walk([d.binders, d.context, d.proof_spans])
                                 if isinstance(n, dict) and n.get("loc") and
                                 isinstance(value(n), list) and value(n) and value(n)[0] in ("Name", "Id")}
                if target_offset in local_offsets:
                    by_path[path].resolution_status[offset] = "local"
    return result


def learning(dictionary, encounters, output):
    items = sorted(encounters.items(), key=lambda x: str(x[0]))
    print("\nRendering dictionary: choose a number to teach/replace, 'remove NUMBER', or 'done'.")
    for i, (key_parts, _) in enumerate(items, 1):
        kind, key, arity, scope, entry = key_parts[:5]
        print(f"{i}: {kind} {key!r} ({arity} slots, scope={scope!r})")
    while True:
        try:
            choice = input("rule> ").strip()
            if choice in ("", "done", "quit"):
                return
            removing = choice.startswith("remove ")
            number = int(choice.split()[-1]) - 1
            if number < 0 or number >= len(items):
                raise DictionaryError("select a listed rule number")
            key_parts, (label, children, source) = items[number]
            kind, key, arity, scope, entry = key_parts[:5]
            selector = {"kind": kind, "key": key, "arity": arity, "scope": scope, "entry": entry}
            if kind == "notation" and label.identity:
                selector["identity"] = label.identity
            current = dictionary.match(kind, key, arity, scope, entry, label.identity)
            if removing:
                if current and input(f"Remove {current['label']!r}? [y/N] ").lower() == "y":
                    dictionary.remove(current)
                    dictionary.save()
                continue
            print("Original:", source)
            for i, child in enumerate(children):
                print(f"Slot {i}:\n{child.plain()}")
            print('Enter JSON with label, layout, slots, optional template (e.g. "{0}={1}") and when; blank skips.')
            text = input("template> ").strip()
            if not text:
                continue
            fields = json.loads(text)
            if not isinstance(fields, dict) or set(fields) - {"label", "layout", "slots", "template", "when"}:
                raise DictionaryError("template accepts only label, layout, slots, template, and when")
            from .dictionary import validate
            rule = validate({**selector, **fields})
            document = dictionary.apply(rule, label, children, proposition=True)
            preview = output / "rule-preview.html"
            output.mkdir(parents=True, exist_ok=True)
            (output / "style.css").write_text(CSS)
            preview.write_text(shell("Rendering rule preview", '<h1>Rendering rule preview</h1><pre>' + render_html(document, preview, {}) + '</pre>', preview, output))
            print(document.plain())
            print(f"HTML preview: {preview}")
            if input("Save this rule? [y/N] ").lower() == "y":
                dictionary.replace(rule)
                dictionary.save()
        except (EOFError, KeyboardInterrupt):
            print("\nLearning cancelled; unaccepted rules were not saved.")
            return
        except (ValueError, DictionaryError) as exc:
            print(f"Invalid rule: {exc}")


class Coverage(dict):
    explanation_failures = 0


def generate(sources, resolutions, dictionary, output, single=None, learn=False, explanation_options=None,
             history_cache=None, history_repository=None, term_view="elaborated"):
    if term_view not in ("elaborated", "source"):
        raise ValueError("term_view must be elaborated or source")
    options = replace(explanation_options) if explanation_options else Options()
    options.validate()
    if options.cache is None:
        options.cache = single.with_suffix(".explanations.json") if single else output / "explanations.json"
    report_path = single.with_suffix(".report.json") if single else output / "report.json"
    if options.cache.suffix != ".json" or options.cache.resolve() in (report_path.resolve(), dictionary.path.resolve()):
        raise ValueError("explanation cache must be a separate .json file, not the report or rendering dictionary")
    history_cache = history_cache or repository(sources[0].root) / "build/prompt-history.json"
    protected = {options.cache.resolve(), report_path.resolve(), dictionary.path.resolve(),
                 *(s.path.resolve() for s in sources)}
    if history_cache.suffix != ".json" or history_cache.resolve() in protected or history_cache.name.endswith("explanations.json"):
        raise ValueError("history cache must be a separate .json file, not an explanation cache, report, dictionary, or source")
    validate_cache_path(history_cache)
    known = identities(sources)
    resolved = resolved_identities(resolutions, sources)
    outputs = {s.path: single if single else output / s.relative.with_suffix(".html") for s in sources}
    if not single:
        reserved = {output / "index.html", output / "declarations.html", output / "rule-preview.html"}
        outputs = {path: target.with_name(target.stem + ".source.html") if target in reserved else target
                   for path, target in outputs.items()}
        if len(set(outputs.values())) != len(outputs):
            raise ValueError("source filenames collide in generated HTML output")
    symbols = {}
    for source in sources:
        for declaration in source.declarations:
            for decl in (declaration, *declaration.children):
                if decl.identity in symbols:
                    raise ValueError(f"duplicate Rocq identity {decl.identity}; check project load-path mappings")
                symbols[decl.identity] = (outputs[source.path], anchor(decl.identity))
    encounters = {}
    def render():
        documents, coverage = {}, Coverage()
        for source in sources:
            adapter = Adapter(source, dictionary, known, resolved.get(source.path))
            documents[source.path] = []
            for decl in source.declarations:
                documents[source.path].append(adapter.declaration(decl))
            coverage[source.path] = adapter.coverage
            encounters.update(adapter.encounters)
        return documents, coverage
    documents, coverage = render()
    if learn:
        learning(dictionary, encounters, single.with_suffix(".preview") if single else output)
        documents, coverage = render()
    graph = build_graph(sources, documents, resolved)
    explanations = explain(sources, documents, graph, options)
    # Explanation inputs and dependency discovery deliberately remain on the
    # unchanged legacy documents above. Display changes must not alter caches.
    from .ownership import skin
    source_details = {}
    display_source_documents = {}
    display_coverage = {}
    from .display import DisplayAdapter
    for source in sources:
        display_adapter = DisplayAdapter(source, dictionary, known, resolved.get(source.path))
        display_source_documents[source.path] = []
        for decl, doc in zip(source.declarations, documents[source.path]):
            details = []
            start = len(display_adapter.coverage)
            display = display_adapter.declaration(decl)
            display_coverage[decl.identity] = display_adapter.coverage[start:]
            display_source_documents[source.path].append(skin(display, details))
            details.extend(display_adapter.details)
            source_details[decl.identity] = details
        coverage[source.path] = display_adapter.coverage
    display_documents = display_source_documents
    elaboration_details = {}
    if term_view == "elaborated":
        from .terms import Renderer, block
        display_documents = {}
        for source in sources:
            coverage[source.path] = []
            rendered = []
            for decl, legacy in zip(source.declarations, documents[source.path]):
                record = source.elaborated.setdefault(decl.identity, {
                    "status": "unavailable", "reason": "No elaborated term was exported.", "unsupported": []})
                if record["status"] == "available":
                    renderer = Renderer(decl, dictionary)
                    try:
                        document = renderer.document(record)
                        record["unsupported"] = sorted(set(renderer.unsupported))
                        elaboration_details[decl.identity] = block("parameters, instances and stored field values", renderer.hidden)
                        rendered.append(document)
                    except (KeyError, ValueError, TypeError, IndexError) as exc:
                        record.update(status="unavailable", reason="Unsupported elaborated term: " + str(exc))
                        rendered.append(display_source_documents[source.path][len(rendered)])
                else:
                    rendered.append(display_source_documents[source.path][len(rendered)])
                if record["status"] != "available":
                    record["unsupported"] = display_coverage.get(decl.identity, [])
                    coverage[source.path].append("elaboration unavailable: " + decl.identity)
                coverage[source.path].extend(record.get("unsupported", []))
            display_documents[source.path] = rendered
    history = collect_history(sources, history_cache, history_repository)
    coverage.explanation_failures = sum(e["status"] == "failed" for e in explanations.values())
    output.mkdir(parents=True, exist_ok=True)
    if not single:
        (output / "style.css").write_text(CSS)
    for source in sources:
        target = outputs[source.path]
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(page(source, display_documents[source.path], target, output, symbols, coverage[source.path],
                               standalone=bool(single), graph=graph, explanations=explanations, history=history,
                               term_view=term_view, elaboration_details=elaboration_details,
                               source_documents=display_source_documents[source.path], ownership_details=source_details))
    if not single:
        (output / "index.html").write_text(index(sources, outputs, output, graph, explanations))
        (output / "declarations.html").write_text(inventory(sources, outputs, output))
    report = {"version": 1, "files": [{"file": str(s.relative), "errors": s.errors,
                "unsupported": sorted(set(coverage[s.path])), "declarations": len(s.declarations)} for s in sources]}
    report["dependencies"] = {"complete": not graph.incomplete, "roots": graph.roots,
                               "source_issues": graph.source_issues,
                               "declarations": {i: {"depends_on": graph.edges[i], "statement_depends_on": graph.statement_edges.get(i, []), "issues": graph.issues[i]} for i in sorted(graph.edges)}}
    report["explanations"] = {"model_selection": options.model or "CLI configured model",
                              "failures": coverage.explanation_failures, "declarations": explanations}
    report["term_view"] = term_view
    report["elaboration"] = {identity: {k: v for k, v in record.items() if k not in ("term", "children")}
                             for source in sources for identity, record in source.elaborated.items()}
    report["cangjie"] = {identity: record for source in sources for identity, record in source.cangjie.items()}
    report["correctness_contracts"] = graph.contracts
    report["history"] = {"complete": all(r["complete"] for r in history.values()), "declarations": history}
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    return coverage


def main(argv=None):
    parser = argparse.ArgumentParser(description="Render proof-free Rocq specifications as linked, offline HTML")
    commands = parser.add_subparsers(dest="command", required=True)
    refresh = commands.add_parser("refresh-history", help="update history in saved HTML, preserving explanations and rendered content")
    refresh.add_argument("--output", type=Path, required=True, help="existing documentation directory or single .html file")
    refresh.add_argument("--history-cache", type=Path)
    refresh.add_argument("--history-repository", type=Path)
    for name in ("build", "render"):
        command = commands.add_parser(name)
        if name == "render":
            command.add_argument("file", type=Path)
            command.add_argument("--name", required=True)
        else:
            command.add_argument("--sources", nargs="+", type=Path,
                                 help="limit the build to these source files or directories")
        command.add_argument("--output", type=Path, default=Path("generated/spec-html") if name == "build" else None,
                             required=name == "render")
        command.add_argument("--dictionary", type=Path, default=DEFAULT_DICTIONARY)
        command.add_argument("--learn", action="store_true")
        command.add_argument("--term-view", choices=("elaborated", "source"), default="elaborated",
                             help="Rocq-elaborated skin (default) or legacy parsed source rendering")
        command.add_argument("--strict", action="store_true")
        command.add_argument("--timeout", type=float, default=600, help="backend request timeout in seconds")
        command.add_argument("--explanations", choices=("auto", "offline"), default="auto",
                             help="generate missing explanations through Codex, or use cached text only")
        command.add_argument("--llm-model", help="Codex model override; default uses CLI configuration")
        command.add_argument("--llm-timeout", type=float, default=120, help="explanation request timeout in seconds")
        command.add_argument("--explanation-cache", type=Path, help="versioned JSON explanation cache path")
        command.add_argument("--history-cache", type=Path, help="separate Git prompt-history JSON cache (default: repository build/prompt-history.json)")
        command.add_argument("--history-repository", type=Path, help="original CJR checkout containing migration-manifest.json and pre-split Git history")
    args = parser.parse_args(argv)
    root = Path.cwd().resolve()
    destination = args.output.resolve()
    if args.command == "refresh-history":
        from .refresh_history import refresh as refresh_saved_history
        try:
            history = refresh_saved_history(root, destination, args.history_cache, args.history_repository)
            incomplete = sum(not r["complete"] for r in history.values())
            print(f"Refreshed history for {len(history)} declarations ({incomplete} incomplete); existing explanations preserved")
            return 0
        except (OSError, ValueError) as exc:
            print(f"rocq-readable: {exc}", file=sys.stderr)
            return 1
    output = destination if args.command == "build" else destination.parent
    try:
        if not math.isfinite(args.timeout) or args.timeout <= 0:
            raise ValueError("timeout must be finite and positive")
        options = Options(args.explanations, args.llm_model, args.llm_timeout,
                          args.explanation_cache.resolve() if args.explanation_cache else None)
        options.validate()
        if args.command == "build" and output == root:
            raise ValueError("output must be a separate directory, not the project root")
        dictionary = Dictionary(args.dictionary.resolve())
        if args.command == "render":
            path = args.file.resolve()
            if not inside(path, root) or path.suffix != ".v" or not path.is_file():
                raise ValueError("input must be a .v file within the current directory")
            if destination.name in ("index.html", "declarations.html", "rule-preview.html") or destination.suffix != ".html":
                raise ValueError("single output must be a .html file other than index.html, declarations.html or rule-preview.html")
            paths = [path]
        else:
            if args.sources:
                paths = []
                for entry in args.sources:
                    entry = entry.resolve()
                    if not inside(entry, root) or not entry.exists():
                        raise ValueError("sources must exist within the current directory")
                    if entry.is_dir():
                        paths.extend(discover(entry, output))
                    elif entry.suffix == ".v":
                        paths.append(entry)
                    else:
                        raise ValueError("sources must be Rocq files or directories")
                paths = sorted(set(paths))
            else:
                paths = discover(root, output)
        if not paths:
            raise ValueError("no Rocq .v sources found beneath the current directory")
        sources, resolutions = prepare(paths, root, args.timeout,
                                       selected=args.name if args.command == "render" else None, term_view=args.term_view)
        if args.command == "render":
            candidates = [d for d in sources[0].declarations if d.identity == args.name or d.name == args.name]
            if len(candidates) != 1:
                raise ValueError(f"expected one declaration named {args.name!r}; candidates: " +
                                 ", ".join(d.identity for d in candidates or sources[0].declarations))
            sources[0].declarations = candidates
        coverage = generate(sources, resolutions, dictionary, output,
                            single=destination if args.command == "render" else None, learn=args.learn,
                            explanation_options=options,
                            history_cache=args.history_cache.resolve() if args.history_cache else None,
                            history_repository=args.history_repository.resolve() if args.history_repository else None,
                            term_view=args.term_view)
        errors = sum(bool(s.errors) for s in sources)
        unsupported = sum(len(c) for c in coverage.values())
        result = destination if args.command == "render" else output / "index.html"
        print(f"Generated {result} ({len(sources)} files, {errors} with errors, {unsupported} unmapped/unsupported constructs, {coverage.explanation_failures} failed explanations)")
        return 1 if errors or coverage.explanation_failures or args.strict and unsupported else 0
    except (OSError, ValueError, BackendError) as exc:
        print(f"rocq-readable: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
