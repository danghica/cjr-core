"""Shared compiler, provenance, and JSON helpers for project instances."""
from __future__ import annotations

import hashlib
import json
import os
import platform
import re
import subprocess
import tempfile
from pathlib import Path

from tools.project_tools.docs import hashes as project_hashes, write_json


def toolchain(project_root: Path, required_version="1.0.5"):
    cjc=Path(os.environ.get("CJC",str(Path.home()/"cangjiebuild/software/cangjie/bin/cjc")))
    home=Path(os.environ.get("CANGJIE_HOME",str(cjc.parent.parent)))
    env=os.environ.copy(); env["CANGJIE_HOME"]=str(home)
    env["DYLD_LIBRARY_PATH"]=str(home/"runtime/lib/darwin_aarch64_cjnative")
    sdk=env.get("SDKROOT")
    if not sdk and platform.system()=="Darwin":
        sdk=Path(subprocess.check_output(["xcrun","--show-sdk-path"],text=True).strip())
        compat=Path(tempfile.gettempdir())/"cjr-project-sdk"
        for stub in (sdk/"usr/lib").rglob("*.tbd"):
            if stub.is_symlink(): continue
            target=compat/stub.relative_to(sdk);target.parent.mkdir(parents=True,exist_ok=True)
            contents=re.sub(r"arm64e\.x1-[\w]+\s*,?\s*", "", stub.read_text())
            contents=re.sub(r",\s*\]", " ]", contents).replace("arm64e-", "arm64-")
            if not target.exists() or target.read_text()!=contents: target.write_text(contents)
        link=compat/"usr/lib/libSystem.tbd"
        if not link.is_symlink(): link.symlink_to("libSystem.B.tbd")
        sdk=compat
    if sdk: env["SDKROOT"]=str(sdk)
    version=subprocess.check_output([str(cjc),"--version"],env=env,text=True).strip()
    if required_version and required_version not in version:
        raise RuntimeError(f"Cangjie {required_version} required; found {version}")
    return cjc,env,version


def hashes(project_root: Path):
    return project_hashes(Path(project_root).resolve())


def metadata(project_root: Path, version: str, flags):
    return {"sources":hashes(project_root),"compiler":version,"flags":list(flags),
            "machine":platform.uname()._asdict(),
            "sdk":os.environ.get("SDKROOT","macOS TAPI compatibility copy: arm64e.x1 removed, arm64e labels normalized to arm64")}


__all__=["toolchain","hashes","metadata","write_json"]
