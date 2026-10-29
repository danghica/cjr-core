#!/usr/bin/env python3
import os,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
CORE=ROOT if (ROOT/'tools/rocq_readable').is_dir() else Path(os.environ.get('CJR_CORE_DIR',ROOT.parent/'cjr-core')).resolve()
if not (CORE/'tools/project_tools/workspace.py').is_file():
    raise SystemExit('Missing CJR core dependency; set CJR_CORE_DIR')
sys.path.insert(0,str(CORE))
os.environ['CJR_PROJECT_ROOT']=str(ROOT)
from tools.project_tools.workspace import main
main(ROOT)
