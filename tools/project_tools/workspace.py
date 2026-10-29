"""Build adapters for split CJR repositories. Runtime/report actions never check proofs."""
from __future__ import annotations
import argparse,csv,hashlib,html,json,os,re,shlex,shutil,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone

CORE=Path(__file__).resolve().parents[2]

def dependencies(root,check=True):
    lock=json.loads((root/'dependencies.lock.json').read_text())
    paths={}
    for name,version in lock.items():
        key={'cjr-core':'CJR_CORE_DIR','cjr-collections':'CJR_COLLECTIONS_DIR'}[name]
        path=Path(os.environ.get(key,root.parent/name)).resolve()
        if not (path/'repository.json').is_file():raise RuntimeError(f'Missing {name}; set {key} to its checkout')
        actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=path,text=True).strip()
        if check and actual!=version:raise RuntimeError(f'{name} version mismatch: expected {version}, found {actual}; use the pinned checkout via {key}')
        paths[name]=path
    return paths

def configure(root,deps):
    name=json.loads((root/'repository.json').read_text())['name']
    core=deps.get('cjr-core',root)
    flags=['-R',str(core/'theories'),'cjr','-Q',str(core/'tools/extraction/rocq'),'cjr.examples']
    for base in [core,*([deps['cjr-collections']] if 'cjr-collections' in deps else []),root]:
        for folder in sorted((base/'example').glob('*/rocq')):
            namespace='cjr.aes_ige' if folder.parent.name=='aes_ige' else 'cjr.examples'
            flags+=['-Q',str(folder),namespace]
        if (base/'example/quadtree').is_dir():flags+=['-Q',str(base/'example/quadtree'),'cjr.quadtree']
        if (base/'example/authenticator/core/rocq').is_dir():flags+=['-Q',str(base/'example/authenticator/core/rocq'),'cjr.authenticator']
    if name!='cjr-core':flags+=['-Q',str(root/'extraction'),'cjr.'+name.removeprefix('cjr-')]
    flags+=['-Q',str(root/'audit'),'cjr.audit']
    pairs=[]
    for i in range(0,len(flags),3):
        triple=tuple(flags[i:i+3])
        if triple not in pairs:pairs.append(triple)
    lines=[' '.join(t) for t in pairs]+['-arg -w','-arg +admitted-proof']
    sources=[]
    for folder in ('theories','tools/extraction/rocq','example','extraction'):
        for p in sorted((root/folder).rglob('*.v')):
            if 'docs' not in p.parts:sources.append(p.relative_to(root).as_posix())
    (root/'_CoqProject').write_text('\n'.join(lines+sources)+'\n')
    # Example configurations use the same explicit dependency paths.
    for example in (root/'example').iterdir():
        if example.is_dir():
            local=[' '.join(t) for t in pairs]
            local += [str(p.relative_to(example)) for p in sorted(example.rglob('*.v')) if 'docs' not in p.parts]
            (example/'_CoqProject').write_text('\n'.join(local)+'\n')
    return [x for t in pairs for x in t],sources

_VERIFY_LOG = None

def run(args,root,**kwargs):
    command=[str(a) for a in args]
    environment=os.environ.copy()
    environment['PATH']=str(Path.home()/'.opam/default/bin')+os.pathsep+environment.get('PATH','')
    kwargs.setdefault('env',environment)
    if _VERIFY_LOG is None:
        subprocess.run(command,cwd=root,check=True,**kwargs)
        return ''
    _VERIFY_LOG.write('Command: '+shlex.join(command)+'\n');_VERIFY_LOG.flush()
    process=subprocess.Popen(command,cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,**kwargs)
    output=[]
    for line in process.stdout:
        _VERIFY_LOG.write(line);_VERIFY_LOG.flush();print(line,end='',flush=True);output.append(line)
    status=process.wait()
    if status:raise subprocess.CalledProcessError(status,command)
    return ''.join(output)

def proof_build(root,deps,verify=False):
    if verify:return verify_proofs(root,deps)
    for name,path in deps.items():
        if name in ('cjr-core','cjr-collections'):run([sys.executable,path/'scripts/project.py','build'],path)
    flags,sources=configure(root,deps)
    (root/'build').mkdir(exist_ok=True)
    maker=shutil.which('coq_makefile') or str(Path.home()/'.opam/default/bin/coq_makefile')
    run([maker,'-f','_CoqProject','-o','CoqMakefile'],root)
    run(['make','-f','CoqMakefile','-j2'],root)
    return flags,sources

def verify_proofs(root,deps):
    global _VERIFY_LOG
    (root/'build').mkdir(exist_ok=True)
    started=datetime.now(timezone.utc).isoformat()
    record={'status':'failed','started_utc':started,'dependencies':json.loads((root/'dependencies.lock.json').read_text()),'coqchk':'not completed','assumptions':'not completed'}
    status=1
    with (root/'build/verify.log').open('w') as log:
        _VERIFY_LOG=log
        log.write('make verify started: '+started+'\n');log.flush()
        try:
            flags,sources=proof_build(root,deps)
            record['sources']={name:hashlib.sha256((root/name).read_bytes()).hexdigest() for name in [*sources,'audit/assumptions.v']}
            record['modules_checked']=len(sources)
            for name in sources:
                source=(root/name).read_text()
                # Ignore comments; reject proof bypasses in executable Rocq text.
                depth=0;clean=[];i=0
                while i<len(source):
                    if source[i:i+2]=='(*':depth+=1;i+=2
                    elif depth and source[i:i+2]=='*)':depth-=1;i+=2
                    else:
                        if not depth:clean.append(source[i])
                        i+=1
                if re.search(r'\b(?:Admitted|admit|Abort)\b|^\s*(?:(?:Local|Global)\s+)?Axioms?\s',''.join(clean),re.M):
                    raise RuntimeError('Disallowed admission, aborted proof, or axiom: '+name)
            prefix=Path.home()/'.opam/default/bin'
            record['toolchain']=subprocess.check_output([str(prefix/'coqc'),'--version'],text=True).strip()
            run([prefix/'coqchk','-silent',*flags,*[str(Path(name).with_suffix('.vo')) for name in sources]],root)
            record['coqchk']='passed'
            audit=run([prefix/'coqc',*flags,'audit/assumptions.v'],root)
            (root/'build/assumptions.log').write_text(audit)
            expected=len(re.findall(r'^Print Assumptions ',(root/'audit/assumptions.v').read_text(),re.M))
            closed=audit.count('Closed under the global context')
            record.update(expected_closed=expected,closed=closed)
            if closed!=expected or re.search(r'^Axioms:|\bError:',audit,re.M):
                raise RuntimeError(f'Assumption audit: {closed}/{expected} declarations closed')
            record['assumptions']='all audited declarations closed under the global context'
            record['status']='passed';status=0
            print(f'Proof validation passed: {len(sources)} modules; {closed}/{expected} assumption audits closed.',flush=True)
        except Exception as error:
            record['error']=str(error);log.write('ERROR: '+str(error)+'\n');raise
        finally:
            finished=datetime.now(timezone.utc).isoformat();record['finished_utc']=finished;record['exit_status']=status
            log.write(f'make verify finished: {finished} (exit status {status})\n');log.flush()
            _VERIFY_LOG=None
            record['verify_log_sha256']=hashlib.sha256((root/'build/verify.log').read_bytes()).hexdigest()
            (root/'build/proof-verification.json').write_text(json.dumps(record,indent=2)+'\n')

def extraction(root,deps):
    proof_build(root,deps)
    from . import examples
    examples.extract()
    if (root/'example/quadtree').exists():
        run([sys.executable,'scripts/extract.py'],root/'example/quadtree')
    if (root/'example/authenticator').exists():run([sys.executable,'example/authenticator/core/scripts/check.py','--extract-only'],root)

def pages(root):
    """Assemble static entry points; never start coq-lsp."""
    cfg=json.loads((root/'repository.json').read_text())
    style='body{max-width:1100px;margin:3rem auto;padding:0 1.5rem;font:18px/1.6 system-ui;color:#172338;background:#fafbfe}a{color:#185a91}h1,h2{line-height:1.2}li{margin:.5rem 0}pre{white-space:pre-wrap;background:#eef2f8;padding:1rem}aside{border-left:4px solid #be8b27;padding:1rem;background:#fff5dc}table{border-collapse:collapse}td,th{padding:.4rem 1rem;border-bottom:1px solid #ddd;text-align:left}'
    docs=root/'docs';docs.mkdir(exist_ok=True);(docs/'style.css').write_text(style)
    proof_path=root/'build/proof-verification.json'
    proof=json.loads(proof_path.read_text()) if proof_path.exists() else {}
    fresh=(proof.get('status')=='passed' and proof.get('dependencies')==json.loads((root/'dependencies.lock.json').read_text()) and all((root/name).is_file() and hashlib.sha256((root/name).read_bytes()).hexdigest()==digest for name,digest in proof.get('sources',{}).items()))
    if fresh:
        intro=f'<aside><strong>Proof validation passed.</strong> {proof["modules_checked"]} modules kernel-checked; {proof["closed"]}/{proof["expected_closed"]} assumption audits closed. Recorded {html.escape(proof["finished_utc"])}. Read the repository README for the verification log and source fingerprints. Imported readable-specification pages remain historical snapshots.</aside>'
    else:
        intro='<aside>Current sources do not have a matching successful proof-validation record. Imported proof and readable-specification reports are historical snapshots. Runtime checks and measurements are reported separately.</aside>'

    links=['<li><a href="../paper/tutorial.pdf">Tutorial paper (PDF)</a> · <a href="../paper/tutorial.tex">LaTeX source</a></li>','<li><a href="../README.md">Setup and commands</a> · <a href="../dependencies.lock.json">Pinned dependencies</a></li>','<li><a href="../build/runtime-validation.json">Runtime validation</a></li>']
    if proof_path.is_file():links.append('<li><a href="../build/proof-verification.json">Proof validation record</a> · <a href="../build/verify.log">Verification log</a></li>')
    for name in cfg['examples']:
        project=root/'example'/name
        entries=[]
        for p in [project/'docs/rocq/index.html',project/'test/report.html',project/'test/results/report.json',project/'docs/guide.html',project/'build/report.json',project/'build/frontend-report.json',project/'benchmark/results/report.html']:
            if p.is_file():entries.append('<li><a href="'+os.path.relpath(p,project)+'">'+html.escape(str(p.relative_to(project)))+'</a></li>')
        for p in sorted(project.rglob('*.cj')):
            if 'results' not in p.parts and 'build' not in p.parts:entries.append('<li><a href="'+os.path.relpath(p,project)+'">'+html.escape(str(p.relative_to(project)))+'</a></li>')
        (project/'index.html').write_text('<!doctype html><html><head><meta charset="utf-8"><title>'+name+'</title><link rel="stylesheet" href="../../docs/style.css"></head><body><a href="../../docs/index.html">Repository documentation</a><h1>'+name+'</h1>'+intro+'<ul>'+''.join(entries)+'</ul></body></html>')
        links.append('<li><a href="../example/'+name+'/index.html">'+name+'</a></li>')
    if (root/'generated/spec-html/index.html').exists():links.append('<li><a href="../generated/spec-html/index.html">Framework specifications (historical HTML)</a></li>')
    if (root/'benchmark/results/report.html').exists():links.append('<li><a href="../benchmark/results/report.html">Core runtime benchmarks</a></li>')
    (docs/'index.html').write_text('<!doctype html><html><head><meta charset="utf-8"><title>'+cfg['name']+'</title><link rel="stylesheet" href="style.css"></head><body><h1>'+cfg['name']+'</h1>'+intro+'<h2>Getting started</h2><p>Run make dependencies to check pinned sibling checkouts. Run make test, make benchmark, make docs, or make paper independently. These commands use the checked-in native sources and do not compile proofs. make build, make extract, make verify, and make readable explicitly invoke the Rocq toolchain.</p><h2>Documentation and results</h2><ul>'+''.join(links)+'</ul><h2>Readable specifications</h2><p>The renderer, launcher, packaging, resources, and tests live exclusively in cjr-core. This repository owns its documentation and cached outputs. make readable invokes the core renderer and checks proofs; it was not run during this migration.</p></body></html>')

def paper(root):
    parts=['\\subsection{Measurement protocol}\nTimings are from optimized Cangjie 1.0.5 builds on the machine recorded in each metadata file. Each suite uses its checked-in configuration, warmups, independent processes, and checksum validation. Medians and interquartile ranges describe repeated samples; they are not universal guarantees.\\par\n']
    for p in sorted(root.rglob('summary.json')):
        if p.parent.name!='results' or not (p.parent/'metadata.json').is_file():continue
        rows=json.loads(p.read_text());meta=json.loads((p.parent/'metadata.json').read_text())
        name=str(p.parent.relative_to(root));esc=lambda s:str(s).replace('_',r'\_').replace('%',r'\%').replace('&',r'\&')
        parts.append('\\subsection{'+esc(name)+'}\nRecorded '+esc(meta.get('date_utc','historical'))+'. '+str(len(rows))+' workload groups. Values below are ns per harness-defined operation. Full results, provenance, and charts are in the local HTML report.\n')
        parts.append('\\begin{longtable}{p{0.57\\textwidth}rr}Workload / implementation & Median & IQR \\\\ \\hline\n')
        for row in rows:
            label=' / '.join(str(row.get(k,'')) for k in meta.get('group_by',[]) if row.get(k) is not None)
            parts.append(esc(label)+f" & {row['median_ns']:.2f} & {row['iqr_ns']:.2f} \\\\\n")
        parts.append('\\end{longtable}\n')
    (root/'paper/current-benchmarks.tex').write_text(''.join(parts))
    for _ in range(2):run(['pdflatex','-interaction=nonstopmode','-halt-on-error','-output-directory=paper','paper/tutorial.tex'],root,stdout=subprocess.DEVNULL)

def main(root):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=['dependencies','build','extract','verify','test','docs','report','paper','benchmark','readable'])
    parser.add_argument('--example');parser.add_argument('--explanations',default='offline')
    args=parser.parse_args();deps=dependencies(root)
    os.environ['CJR_CORE_DIR']=str(deps.get('cjr-core',root))
    os.environ['CJR_PROJECT_ROOT']=str(root)
    if 'cjr-collections' in deps:os.environ['CJR_COLLECTIONS_DIR']=str(deps['cjr-collections'])
    os.environ['PYTHONPATH']=str(CORE)+os.pathsep+os.environ.get('PYTHONPATH','')
    if args.command=='dependencies':
        configure(root,deps);print('Dependencies match lock file');return
    if args.command in ('build','verify'):proof_build(root,deps,args.command=='verify');return
    if args.command=='extract':extraction(root,deps);return
    names=json.loads((root/'repository.json').read_text())['examples']
    if args.example:
        if args.example not in names:raise RuntimeError('Unknown example '+args.example)
        names=[args.example]
    from . import examples,benchmark
    if args.command=='test':
        results=[]
        for name in names:
            if name=='authenticator':run([sys.executable,'example/authenticator/core/scripts/check.py','--test-only'],root)
            else:examples.runtime_tests(name)
            results.append({'example':name,'status':'passed'})
        (root/'build').mkdir(exist_ok=True)
        (root/'build/runtime-validation.json').write_text(json.dumps({'date_utc':datetime.now(timezone.utc).isoformat(),'proofs_revalidated':False,'results':results},indent=2)+'\n')
    if args.command=='benchmark':
        configs=[root/'example'/name/'benchmark/benchmark.config.json' for name in names]
        if not args.example:configs+=[root/'benchmark/benchmark.config.json']
        for config in configs:
            if config.exists():benchmark.run(config);benchmark.plot(config);benchmark.report(config)
    if args.command=='readable':
        configure(root,deps)
        for name in names:examples.readable(name,args.explanations)
        if json.loads((root/'repository.json').read_text())['name']=='cjr-core':run([sys.executable,'-m','tools.rocq_readable','build','--sources','theories','tools/extraction/rocq','--output','generated/spec-html','--explanations',args.explanations],root)
    if args.command=='paper':paper(root)
    if args.command in ('docs','report','benchmark','test','paper'):
        pages(root)
        from .link_audit import audit
        result=audit(root)
        (root/'docs/link-check.json').write_text(json.dumps(result,indent=2)+'\n')
        if result['errors']:raise RuntimeError(f"{len(result['errors'])} broken documentation links; see docs/link-check.json")

if __name__=='__main__':main(Path.cwd())
