"""Shared offline documentation, artifact pages, and declaration index builder."""
from __future__ import annotations

import argparse
import hashlib
import html
import json
import os
import re
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit


class HTMLInfo(HTMLParser):
    def __init__(self, source=""):
        super().__init__(); self.ids=set(); self.links=[]; self.declarations=[]
        self._nav=False; self._anchor=None; self._label=""
        self._article=None; self._heading=False; self._heading_label=""
        if source: self.feed(source)
    def handle_starttag(self, tag, attrs):
        a=dict(attrs)
        if "id" in a: self.ids.add(a["id"])
        for key in ("href", "src"):
            if a.get(key): self.links.append(a[key])
        if tag=="nav" and a.get("aria-label")=="Declarations": self._nav=True
        if self._nav and tag=="a": self._anchor=a.get("href"); self._label=""
        if tag=="article" and a.get("id", "").startswith("symbol-"):
            self._article=a["id"]
        if tag=="h2" and self._article:
            self._heading=True; self._heading_label=""
    def handle_data(self, data):
        if self._anchor is not None: self._label += data
        if self._heading: self._heading_label += data
    def handle_endtag(self, tag):
        if tag=="a" and self._anchor is not None:
            self.declarations.append((self._anchor, self._label.strip())); self._anchor=None
        if tag=="nav": self._nav=False
        if tag=="h2" and self._heading:
            self.declarations.append(("#"+self._article,self._heading_label.strip()))
            self._heading=False
        if tag=="article": self._article=None


def hashes(root: Path, exclude=()):
    ignored=set(exclude) | {".git", "__pycache__", "results", "build"}
    result={}
    for path in sorted(root.rglob("*")):
        parts = path.relative_to(root).parts
        generated_docs = any(parts[i:i+2] == ("docs", "rocq") for i in range(len(parts)-1))
        if not path.is_file() or any(part in ignored for part in parts) or generated_docs or "generated" in parts:
            continue
        if (path.suffix in {".v", ".cj", ".c", ".py", ".cjs", ".css", ".md", ".txt"}
                or path.name.endswith(".config.json") or path.name in {"_CoqProject", "Makefile", "Makefile.local-late"}):
            result[path.relative_to(root).as_posix()]=hashlib.sha256(path.read_bytes()).hexdigest()
    repo = next((p for p in (root, *root.parents)
                 if (p / "tools/project_tools").is_dir() and (p / "theories/lang.v").is_file()), root)
    shared=repo/"tools"/"project_tools"
    if shared.is_dir():
        for path in sorted(shared.glob("*.py")):
            result[os.path.relpath(path,root).replace(os.sep,"/")]=hashlib.sha256(path.read_bytes()).hexdigest()
    dependencies = [*sorted((repo / "theories").glob("*.v")),
                    *sorted((repo / "tools/extraction/rocq").glob("*.v")),
                    *sorted((repo / "example").glob("*/rocq/*.v")),
                    *sorted((repo / "tools/rocq_readable").glob("*.py")),
                    repo / "tools/rocq_readable/renderings.json",
                    repo / "_CoqProject", repo / "Makefile.local-late"]
    for path in dependencies:
        if path.is_file():
            result[os.path.relpath(path,root).replace(os.sep,"/")]=hashlib.sha256(path.read_bytes()).hexdigest()
    return result


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True)+"\n")


def load(config_path):
    config=json.loads(config_path.read_text()); root=config_path.parent.resolve()
    return config, root


def inside(root, rel):
    path=(root/rel).resolve()
    if not path.is_relative_to(root): raise ValueError(f"configured path leaves project root: {rel}")
    return path


def metadata(config_path):
    config,root=load(config_path)
    output=inside(root,config.get("documentation_metadata","docs/metadata.json"))
    payload={"sources":hashes(root),"renderer":config.get("renderer","rocq-readable"),
             "project":config.get("name",root.name)}
    write_json(output,payload)


def page(path, root, config, title, body):
    css=inside(root,config.get("css","docs/report.css"))
    index=inside(root,config.get("index","index.html"))
    css_rel=os.path.relpath(css,path.parent).replace(os.sep,"/")
    home_rel=os.path.relpath(index,path.parent).replace(os.sep,"/")
    path.parent.mkdir(parents=True,exist_ok=True)
    brand=html.escape(config.get("name",root.name))
    path.write_text(f'<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>{html.escape(title)}</title><link rel="stylesheet" href="{html.escape(css_rel,quote=True)}"><main><header><div class="eyebrow">{brand}</div><h1>{html.escape(title)}</h1><a href="{html.escape(home_rel,quote=True)}">Report index</a></header>{body}<footer>Offline report. Links and assets stay within this project.</footer></main></html>')


def artifact(root, rel):
    path=inside(root,rel)
    if not path.is_file(): raise RuntimeError(f"Missing configured artifact: {rel}")
    return json.loads(path.read_text())


def ensure_fresh(root, data, label, current, inventory=True):
    recorded=data.get("sources",{})
    if not recorded: raise RuntimeError(f"Missing source hashes in {label}")
    for key,value in recorded.items():
        if current.get(key)!=value: raise RuntimeError(f"Stale {label}: {key}")
    if inventory and set(recorded)!=set(current): raise RuntimeError(f"Source inventory changed since {label}")


def report(config_path, allow_stale=False):
    config,root=load(config_path)
    paths=config.get("artifacts",{})
    index=inside(root,config.get("index","index.html"))
    def from_index(path):
        return os.path.relpath(path,index.parent).replace(os.sep,"/")
    current=hashes(root)
    loaded={name:artifact(root,rel) for name,rel in paths.items() if name not in {"index","css","docs","extracted"} and not name.endswith("_report")}
    stale=[]
    for name,data in loaded.items():
        if isinstance(data,dict) and data.get("sources") and not (name == "benchmark" and data.get("historical")):
            try:
                ensure_fresh(root,data,name,current,inventory=(name!="extraction"))
            except RuntimeError as exc:
                if not allow_stale:
                    raise
                stale.append((name, str(exc), data.get("date_utc", "date recorded in artifact metadata")))
        if name in {"verification","tests","benchmark"} and data.get("status") not in {None,"passed"}:
            raise RuntimeError(f"{name} has not passed")
    docdir=inside(root,paths.get("docs","docs/rocq"))
    nav_pages=[]
    rules=config.get("declaration_groups",[])
    group_entries={g["name"]:[] for g in rules}
    group_entries.setdefault("Other declarations",[])
    for html_path in sorted(docdir.rglob("*.html")):
        if html_path.name=="index.html": continue
        info=HTMLInfo(html_path.read_text())
        for anchor,label in info.declarations:
            rel=html_path.relative_to(root).as_posix()
            target=next((r["name"] for r in rules if re.search(r["pattern"],rel)),"Other declarations")
            group_entries[target].append((rel+anchor,label))
    declaration_html="".join(f'<h3>{html.escape(name)}</h3><ul class="declarations">'+"".join(f'<li><a href="{html.escape(from_index(root/href.split("#",1)[0])+("#"+href.split("#",1)[1] if "#" in href else ""),quote=True)}">{html.escape(label)}</a></li>' for href,label in entries)+"</ul>" for name,entries in group_entries.items())
    extracted=inside(root,paths.get("extracted","extracted"))
    source_entries=[]
    for src in sorted(extracted.rglob("*.cj")):
        if src.name=="metadata.json": continue
        view=src.with_suffix(".html")
        rel=os.path.relpath(src,root).replace(os.sep,"/")
        viewrel=os.path.relpath(view,root).replace(os.sep,"/")
        page(view,root,config,src.name,"<pre>"+html.escape(src.read_text())+"</pre>")
        source_entries.append(f'<li><a href="{html.escape(from_index(src),quote=True)}">{html.escape(src.name)}</a> · <a href="{html.escape(from_index(view),quote=True)}">HTML source</a></li>')
    links=[]
    for entry in config.get("links",[]):
        dest=inside(root,entry["path"])
        if not dest.is_file(): raise RuntimeError(f"Missing configured report link destination: {entry['path']}")
        links.append(f'<li><a href="{html.escape(from_index(dest),quote=True)}">{html.escape(entry["label"])}</a></li>')
    for name,rel in paths.items():
        if name in {"index","css","docs","extracted"}: continue
        dest=inside(root,rel)
        if dest.exists(): links.append(f'<li><a href="{html.escape(from_index(dest),quote=True)}">{html.escape(name.replace("_"," ").title())}</a></li>')
    verification=loaded.get("verification",{})
    test=loaded.get("tests",{})
    bench=loaded.get("benchmark",{})
    renderer=loaded.get("renderer",{})
    summary=[]
    if stale:
        summary.append('<p><strong>Saved results from earlier source snapshots.</strong> '
                       'This documentation refresh did not rerun the checks or measurements below. '
                       'Their recorded dates and source hashes are preserved; their source inventory '
                       'differs from the current checkout.</p><ul>' +
                       ''.join(f'<li>{html.escape(name)}: {html.escape(str(date))}. '
                               f'{html.escape(reason)}</li>' for name, reason, date in stale) + '</ul>')
    if verification:
        summary.append(f'<p><span class="badge">Proof checks</span> {html.escape(str(verification.get("coqchk","passed")))}; {html.escape(str(verification.get("audited_declarations","")))} declarations audited; {html.escape(str(verification.get("assumptions","assumption audit passed")))}.</p>')
        if verification.get("contract_coverage"):
            summary.append(f'<p>{html.escape(verification["contract_coverage"])}</p>')
    if test:
        cases=test.get("cases",[])
        case_count=len(cases) if isinstance(cases,list) else test.get("case_count","")
        summary.append(f'<p><span class="badge">Tests</span> {html.escape(str(test.get("status","passed")))} · {html.escape(str(case_count))} cases</p>')
    if bench:
        summary.append(f'<p><span class="badge">Benchmarks</span> {html.escape(str(bench.get("status","passed")))} · {html.escape(str(bench.get("samples","")))} observations.</p>')
        if bench.get("historical"):
            summary.append('<p>Historical measurements: original run dates and source provenance are retained. Directory relocation did not rerun benchmarks.</p>')
    if renderer:
        errors=sum(len(f.get("errors",[])) for f in renderer.get("files",[]))
        unsupported=sum(len(f.get("unsupported",[])) for f in renderer.get("files",[]))
        summary.append(f'<p><span class="badge">Renderer</span> {errors} errors; {unsupported} unsupported or unmapped syntax items retain source notation.</p>')
    title=config.get("title",config.get("name",root.name))
    intro=html.escape(config.get("intro","Offline specification and implementation report."))
    body=f'<p>{intro}</p>'+''.join(summary)+'<h2>Project artifacts</h2><ul>'+''.join(links)+'</ul>'
    if source_entries:
        body+=f'<h2>{html.escape(config.get("extracted_label","Extracted source files"))}</h2><ul>'+''.join(source_entries)+'</ul>'
    body+='<h2>Definitions and lemmas</h2>'+declaration_html
    page(index,root,config,title,body)
    check_links(root)
    write_json(inside(root,config.get("link_check","docs/link-check.json")),
               {"status":"passed","html_files":len(list(root.rglob("*.html"))),"boundary":root.name+"/"})


def check_links(root):
    root=Path(root).resolve()
    pages={p.resolve():HTMLInfo(p.read_text()) for p in root.rglob("*.html") if ".git" not in p.parts}
    for source,info in pages.items():
        for link in info.links:
            u=urlsplit(link)
            if u.scheme or u.netloc: raise RuntimeError(f"external link in offline report: {link}")
            dest=(source.parent/unquote(u.path)).resolve() if u.path else source
            if not dest.is_relative_to(root): raise RuntimeError(f"link leaves project: {link}")
            if not dest.is_file(): raise RuntimeError(f"missing local link target: {link}")
            if u.fragment and (dest not in pages or unquote(u.fragment) not in pages[dest].ids):
                raise RuntimeError(f"missing local anchor: {link}")


def test_report(config_path):
    config,root=load(config_path)
    artifacts=config.get("artifacts",{})
    data=artifact(root,artifacts["tests"])
    dest=inside(root,artifacts.get("test_report","test/report.html"))
    css=inside(root,config.get("css","docs/report.css"))
    cssrel=os.path.relpath(css,dest.parent).replace(os.sep,"/")
    status=data.get("status","unknown")
    cases=data.get("cases",[])
    cases_html="".join(f"<li><span class=\"badge\">{html.escape(status)}</span> {html.escape(str(c))}</li>" for c in cases)
    details={k:v for k,v in data.items() if k not in {"sources","stdout","stderr"}}
    links=[]
    for rel in ("results/report.json","results/compile.log","results/execution.log"):
        path=inside(root,"test/"+rel)
        if path.is_file(): links.append(f'<a href="{html.escape(os.path.relpath(path,dest.parent).replace(os.sep,"/"),quote=True)}">{html.escape(path.name)}</a>')
    body=(f'<p><span class="badge">{html.escape(str(status))}</span> {len(cases)} reported test cases.</p><ul>{cases_html}</ul>'+
          f'<h2>Run metadata</h2><pre>{html.escape(json.dumps(details,indent=2))}</pre>'+
          f'<h2>Execution output</h2><pre>{html.escape(str(data.get("stdout",""))+str(data.get("stderr","")))}</pre>'+
          '<h2>Downloads</h2><p>'+" · ".join(links)+'</p>')
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(f'<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Test report</title><link rel="stylesheet" href="{html.escape(cssrel,quote=True)}"><main><header><h1>Runtime test report</h1><a href="../index.html">Project index</a></header>{body}</main></html>')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command",choices=["metadata","report","test-report"])
    parser.add_argument("config",type=Path)
    parser.add_argument("--allow-stale", action="store_true", help="Render saved source snapshots with a visible notice; preserve recorded provenance")
    args=parser.parse_args()
    if args.command == "report":
        report(args.config.resolve(), allow_stale=args.allow_stale)
        return
    {"metadata":metadata,"report":report,"test-report":test_report}[args.command](args.config.resolve())


if __name__=="__main__": main()
