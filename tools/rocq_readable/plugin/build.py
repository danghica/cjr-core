"""Build the version-pinned Rocq exporter without changing the opam switch."""
from __future__ import annotations

import fcntl
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def build(output=None):
    source = Path(__file__).with_name('export.mlg')
    checkout = source.parents[3]
    if (checkout / '.git').exists():
        default = checkout / 'build/readable-plugin'
    else:
        location = hashlib.sha256(str(source).encode()).hexdigest()[:12]
        default = Path(tempfile.gettempdir()) / ('rocq-readable-plugin-' + location)
    output = Path(output or default).resolve()
    binary = shutil.which('coqc') or str(Path.home() / '.opam/default/bin/coqc')
    bindir = Path(binary).parent
    env = dict(os.environ, PATH=str(bindir) + os.pathsep + os.environ.get('PATH', ''))
    version = subprocess.run([binary, '--version'], capture_output=True, text=True,
                             check=True, env=env, timeout=10).stdout
    if 'version 8.20.' not in version:
        raise RuntimeError('The readable exporter requires Coq 8.20.x')
    compiler = subprocess.run([str(bindir / 'ocamlopt'), '-version'], capture_output=True,
                              text=True, check=True, env=env, timeout=10).stdout
    fingerprint = hashlib.sha256(source.read_bytes() + Path(__file__).read_bytes()
                                 + version.encode() + compiler.encode()).hexdigest()
    package = output / 'rocq-readable'
    package.mkdir(parents=True, exist_ok=True)
    target, stamp = package / 'readable_export.cmxs', package / 'fingerprint'
    # Concurrent documentation/test processes must not load a half-built plugin.
    with (output / '.build.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if target.exists() and (package / 'ReadablePlugin.vo').exists() and stamp.exists() and stamp.read_text() == fingerprint:
            return output
        stamp.unlink(missing_ok=True)
        shutil.copyfile(source, package / 'readable_export.mlg')
        subprocess.run([str(bindir / 'coqpp'), 'readable_export.mlg'], cwd=package,
                       env=env, check=True, timeout=60)
        subprocess.run([str(bindir / 'ocamlfind'), 'ocamlopt', '-rectypes', '-thread', '-w', '-a',
                        '-package', 'coq-core.vernac,coq-core.toplevel,yojson', '-shared',
                        '-o', 'readable_export.cmxs', 'readable_export.ml'], cwd=package,
                       env=env, check=True, timeout=60)
        (package / 'META').write_text('package "export" (\n  requires = "coq-core.vernac coq-core.toplevel yojson"\n  plugin(native) = "readable_export.cmxs"\n)\n')
        wrapper = package / 'ReadablePlugin.v'
        wrapper.write_text('Declare ML Module "rocq-readable.export".\n')
        env['OCAMLPATH'] = str(output) + os.pathsep + env.get('OCAMLPATH', '')
        subprocess.run([binary, '-Q', '.', 'RocqReadable', 'ReadablePlugin.v'], cwd=package,
                       env=env, check=True, timeout=60)
        wrapper.unlink()  # Internal bootstrap must not enter project discovery.
        stamp.write_text(fingerprint)
    return output


if __name__ == '__main__':
    print(build(sys.argv[1] if len(sys.argv) > 1 else None))
