#!/usr/bin/env python3
"""Compile unchanged extracted declarations with only demo mains removed."""
import json,os,re,subprocess,sys,tempfile
from pathlib import Path
compiler,root,binary=sys.argv[1:];root=Path(root)
core=Path(os.environ.get('CJR_CORE_DIR',root if root.name=='cjr-core' else root.parent/'cjr-core'))
config=json.loads((Path(__file__).parent/'benchmark.config.json').read_text())
with tempfile.TemporaryDirectory(prefix='cjr-split-bench-') as scratch:
    paths=[];seen=set()
    for i,name in enumerate(config['libraries']):
        source=(root/name).read_text()
        match=re.search(r'^main\(\)(?:\s*:\s*Unit)?\s*\{',source,re.M)
        if match:
            # Emitted demo main is the final declaration.
            start=match.start();depth=0;end=None
            for pos in range(source.index('{',start),len(source)):
                depth+=(source[pos]=='{')-(source[pos]=='}')
                if depth==0:end=pos+1;break
            if end is None or source[end:].strip():raise RuntimeError('Expected a final demo main')
            source=source[:start]
        def unique(m):
            line=m.group(0)
            if line in seen:return ''
            seen.add(line);return line
        source=re.sub(r'^foreign func .*$',unique,source,flags=re.M)
        p=Path(scratch)/f'library{i}.cj';p.write_text(source);paths.append(str(p))
    helper=core/'tools/project_tools/benchmark_common.cj'
    command=[compiler,*paths,str(helper),str(Path(__file__).parent/config['harness']),'--test','-O2','-o',binary]
    subprocess.run(command,check=True)
