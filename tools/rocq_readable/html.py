"""Portable static HTML; all navigation is relative to generated pages."""
from __future__ import annotations

import html
import json
import os
from pathlib import Path
from urllib.parse import quote

from .layout import Token, anchor, render_html, tokens_html
from .diagram import CSS as GRAPH_CSS, SCRIPT as GRAPH_SCRIPT, panel as graph_panel


def source_excerpt(source, decl, document, current, symbols):
    data = decl.source.encode()
    start, end = decl.source_start, decl.source_start + len(data)
    bindings = {token.anchor for _, tokens in document.lines() for token in tokens if token.anchor}
    local = {identity: f"{anchor(decl.identity)}-binder-{offset}"
             for offset, (identity, kind) in source.glob.definitions.items()
             if kind in ("binder", "var") and f"{anchor(decl.identity)}-binder-{offset}" in bindings}
    tokens, cursor = [], start
    for offset, (stop, identity, kind) in sorted(source.glob.references.items()):
        if offset < cursor or offset < start or stop > end:
            continue
        tokens.append(Token(data[cursor - start:offset - start].decode()))
        text = data[offset - start:stop - start].decode()
        tokens.append(Token(text, local=local.get(identity)) if kind == "var" else Token(text, identity=identity))
        cursor = stop
    tokens.append(Token(data[cursor - start:].decode()))
    return tokens_html(tokens, current, symbols)


CSS = """/* Offline, indentation-preserving specification pages. */
:root { color-scheme: light; font-family: system-ui, sans-serif; color: #203044; background: #f3f5f7; }
body { margin: 0; overflow-wrap: anywhere; } main { max-width: 1080px; margin: auto; padding: 36px 24px 72px; }
header { margin-bottom: 32px; border-bottom: 2px solid #183c52; padding-bottom: 20px; }
.eyebrow { color: #42716c; text-transform: uppercase; letter-spacing: .12em; font-size: .75rem; font-weight: 700; }
h1 { font-size: 2rem; overflow-wrap: anywhere; } h2 { font-size: 1.25rem; margin-top: 0; }
a { color: #006a75; text-decoration-thickness: 1px; text-underline-offset: 3px; }
a:hover { color: #003e49; background: #e2f3ef; } a:focus-visible { outline: 2px solid #006a75; }
article, .panel { background: white; padding: 24px; border: 1px solid #d8e1e5; border-radius: 8px; margin: 20px 0; }
article:target, span:target { outline: 2px solid #67aaa0; scroll-margin-top: 20px; }
pre { font: 14px/1.65 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; white-space: pre; overflow-x: auto; tab-size: 4; }
pre a { text-decoration-style: dotted; } .external { color: #526276; } .unsupported, .error { color: #94392c; }
.meta, .notice { color: #586778; font-size: .9rem; } .notice { line-height: 1.5; }
details { border-top: 1px solid #e1e7eb; padding-top: 12px; } summary { cursor: pointer; font-size: .85rem; color: #586778; }
nav ul, .files { padding-left: 22px; line-height: 1.9; } .count { color: #586778; font-size: .85rem; }
.dependency-tree, .dependency-tree ul { padding-left: 22px; line-height: 1.8; }
.dependency-tree li { overflow-wrap: anywhere; }
.dependency-tree details { border: 0; padding: 0; }
.dependency-tree summary { font-size: 1rem; }
.explanation { line-height: 1.65; }
.explanation-label { font-size: .8rem; font-weight: 700; color: #42716c; }
@media(max-width: 600px) { main { padding: 20px 12px; } article { padding: 16px; } h1 { font-size: 1.5rem; } }
""" + GRAPH_CSS


def relative(target, current):
    return quote(os.path.relpath(target, current.parent).replace(os.sep, "/"), safe="/")


def shell(title, body, current, output, standalone=False):
    stylesheet = relative(output / "style.css", current)
    style = f'<style>{CSS}</style>' if standalone else f'<link rel="stylesheet" href="{stylesheet}">'
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)} — Rocq Readable</title>{style}</head>
<body><main>{body}</main></body></html>
'''


def navigation(current, output):
    return f'<nav aria-label="Project"><a href="{relative(output / "index.html", current)}">Home</a> · <a href="{relative(output / "declarations.html", current)}">Index</a></nav>'


def dependency_links(identities, current, symbols):
    return ''.join('<li>' + declaration_link(i, current, symbols) + '</li>' for i in identities)


def declaration_link(identity, current, symbols):
    target, target_anchor = symbols[identity]
    return f'<a href="{relative(target, current)}#{target_anchor}">{html.escape(identity)}</a>'


def diagram_data(sources, current, symbols, graph):
    included = {d.identity for s in sources for d in s.declarations}
    nodes = {}
    for source in sources:
        for decl in source.declarations:
            target, target_anchor = symbols[decl.identity]
            destination = '' if target == current else relative(target, current)
            nodes[decl.identity] = {"label": decl.identity, "name": decl.name, "kind": decl.kind,
                "file": str(source.relative), "href": destination + '#' + target_anchor,
                "dependencies": [i for i in graph.edges[decl.identity] if i in included]}
    encoded = json.dumps(nodes, ensure_ascii=True, sort_keys=True).replace('<', '\\u003c').replace('>', '\\u003e').replace('&', '\\u0026')
    return '<script id="dependency-data" type="application/json">' + encoded + '</script>'


def file_diagram(source, current, symbols, graph):
    return graph_panel(local=True) + diagram_data([source], current, symbols, graph) + GRAPH_SCRIPT


def page(source, documents, current, output, symbols, coverage, standalone=False, graph=None, explanations=None):
    declarations = source.declarations
    project_nav = '' if standalone else navigation(current, output)
    body = f'''<header><div class="eyebrow">Rocq Readable · specification reference</div>
{project_nav}
<h1>{html.escape(str(source.relative))}</h1><p class="meta">{len(declarations)} declarations · proofs omitted</p>
<p class="notice">Indentation determines multiline scope. Brackets delimit scope only within a line.
WP contracts express partial correctness, without a termination guarantee. Unlinked names may belong to external libraries or remain unresolved.
Rendering rules are presentation choices reviewed by their authors.</p></header>'''
    if graph:
        body += file_diagram(source, current, symbols, graph)
    if source.errors:
        body += '<section class="panel error"><h2>Source errors</h2><ul>' + ''.join('<li>' + html.escape(e) + '</li>' for e in source.errors) + '</ul></section>'
    if coverage:
        body += f'<p class="notice">Incomplete rendering: {len(coverage)} unsupported or unmapped constructs. Original syntax is retained where needed.</p>'
    for decl, document in zip(declarations, documents):
        body += f'<article id="{anchor(decl.identity)}"><h2>{html.escape(decl.name)}</h2><p class="meta">{html.escape(decl.identity)}'
        if decl.section:
            body += ' · ' + html.escape(decl.section)
        body += '</p>'
        explanation = (explanations or {}).get(decl.identity, {})
        body += '<div class="explanation-label">AI-generated explanation</div>'
        if explanation.get("description"):
            body += '<p class="explanation">' + html.escape(explanation["description"]) + '</p>'
        else:
            body += '<p class="notice">Explanation unavailable: ' + html.escape(explanation.get("reason") or "No explanation was generated.") + '</p>'
        body += '<pre class="pseudocode">' + render_html(document, current, symbols) + '</pre>'
        if graph:
            body += '<section aria-label="Direct dependencies"><h3>Depends on</h3>'
            body += '<ul>' + dependency_links(graph.edges[decl.identity], current, symbols) + '</ul>' if graph.edges[decl.identity] else '<p class="meta">No resolved project dependencies.</p>'
            body += ''.join('<p class="notice">' + html.escape(issue) + '</p>' for issue in graph.issues[decl.identity])
            body += '</section>'
        body += '<details><summary>Original declaration (proof-free)</summary><pre>' + source_excerpt(source, decl, document, current, symbols) + '</pre></details></article>'
    return shell(str(source.relative), body, current, output, standalone)


TREE_SCRIPT = """<script>
(() => {
  const graph = JSON.parse(document.getElementById('dependency-data').textContent);
  const tree = document.querySelector('.dependency-tree');
  function entry(identity, path) {
    const node = graph[identity];
    const li = document.createElement('li');
    const link = document.createElement('a');
    link.href = node.href;
    link.textContent = node.label;
    const recursive = path.includes(identity);
    if (node.dependencies.length && !recursive) {
      const details = document.createElement('details');
      details.dataset.identity = identity;
      details.dataset.path = JSON.stringify([...path, identity]);
      const summary = document.createElement('summary');
      summary.append(link);
      details.append(summary);
      li.append(details);
    } else {
      li.append(link);
      if (recursive) li.append(document.createTextNode(' (recursive reference)'));
    }
    return li;
  }
  tree.addEventListener('toggle', event => {
    const details = event.target;
    if (details.tagName !== 'DETAILS' || !details.open || details.dataset.loaded) return;
    const children = document.createElement('ul');
    const path = JSON.parse(details.dataset.path);
    for (const child of graph[details.dataset.identity].dependencies) children.append(entry(child, path));
    details.append(children);
    details.dataset.loaded = 'true';
  }, true);
})();
</script>"""


def index(sources, outputs, output, graph=None):
    current = output / "index.html"
    count = sum(len(s.declarations) for s in sources)
    body = f'''<header><div class="eyebrow">Rocq Readable</div><h1>Project specifications</h1>
{navigation(current, output)}
<p class="meta">{len(sources)} source files · {count} declarations · proofs omitted</p>
<p class="notice">Sources are discovered beneath the invocation directory. Symbol links remain within these generated files; library references are unlinked.</p></header>
'''
    if graph:
        targets = {d.identity: (outputs[s.path], anchor(d.identity)) for s in sources for d in s.declarations}
        body += graph_panel()
        body += '<section class="panel"><h2>Dependency hierarchy</h2><p class="notice">Expand an entry to see what it depends on. Shared dependencies appear under each parent. The <a href="declarations.html">Index</a> lists every declaration.</p>'
        if graph.incomplete:
            body += '<p class="notice">Dependency coverage is incomplete for some declarations. See their notices and report.json.</p>'
        body += '<ul class="dependency-tree">'
        for identity in graph.roots:
            link = declaration_link(identity, current, targets)
            if graph.edges[identity]:
                body += '<li><details data-identity="' + html.escape(identity, quote=True) + '" data-path="' + html.escape(json.dumps([identity]), quote=True) + '"><summary>' + link + '</summary></details></li>'
            else:
                body += '<li>' + link + '</li>'
        body += '</ul><noscript><p>Enable JavaScript to expand the hierarchy. Every declaration page also lists direct dependencies.</p></noscript></section>'
        body += diagram_data(sources, current, targets, graph) + TREE_SCRIPT + GRAPH_SCRIPT
    body += '<section class="panel"><h2>Source files</h2><ul class="files">'
    for source in sources:
        target = outputs[source.path]
        status = " · source errors" if source.errors else ""
        body += f'<li><a href="{relative(target, current)}">{html.escape(str(source.relative))}</a> <span class="count">{len(source.declarations)} declarations{status}</span></li>'
    return shell("Project specifications", body + '</ul></section>', current, output)


def inventory(sources, outputs, output):
    current = output / "declarations.html"
    body = '<header><div class="eyebrow">Rocq Readable</div><h1>Index</h1>' + navigation(current, output) + '</header>'
    body += '<section class="panel"><h2>All declarations</h2><ul class="files">'
    for identity, source, decl in sorted((d.identity, s, d) for s in sources for d in s.declarations):
        body += f'<li><a href="{relative(outputs[source.path], current)}#{anchor(identity)}">{html.escape(identity)}</a> <span class="count">{html.escape(decl.kind)} · {html.escape(str(source.relative))}</span></li>'
    return shell("Index", body + '</ul></section>', current, output)
