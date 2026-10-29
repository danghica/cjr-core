"""Filesystem boundaries, Rocq configuration, and digest-checked symbol data."""
from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import os
from pathlib import Path
import re
import shlex


def inside(path: Path, root: Path) -> bool:
    return path.resolve().is_relative_to(root.resolve())


def discover(root: Path, output: Path) -> list[Path]:
    result = []
    for directory, dirs, files in os.walk(root, followlinks=False):
        base = Path(directory)
        dirs[:] = sorted(d for d in dirs if d != ".git" and
                         (base / d).resolve() != output.resolve() and
                         not (base / d).is_symlink())
        for name in sorted(files):
            path = base / name
            if path.suffix == ".v" and inside(path, root) and not path.is_symlink():
                result.append(path)
    return sorted(result)


def configuration(path: Path, root: Path) -> Path:
    for ancestor in (path.parent, *path.parent.parents):
        if not ancestor.is_relative_to(root):
            break
        for name in ("_RocqProject", "_CoqProject"):
            if (ancestor / name).is_file():
                return ancestor / name
    return root / "_CoqProject"


def module_name(path: Path, config: Path, root: Path) -> str:
    path, root = path.resolve(), root.resolve()
    if config.is_file():
        tokens = shlex.split(config.read_text(), comments=True)
        mappings = []
        for i, token in enumerate(tokens[:-2]):
            if token in ("-R", "-Q"):
                physical = (config.parent / tokens[i + 1]).resolve()
                if path.is_relative_to(physical):
                    relative = path.relative_to(physical).with_suffix("")
                    mappings.append((len(physical.parts), ".".join([tokens[i + 2], *relative.parts])))
        if mappings:
            return max(mappings)[1]
    return ".".join(path.relative_to(root).with_suffix("").parts)


@dataclass
class Glob:
    module: str = ""
    definitions: dict[int, tuple[str, str]] = field(default_factory=dict)
    references: dict[int, tuple[int, str, str]] = field(default_factory=dict)
    valid: bool = False

    @classmethod
    def load(cls, path: Path, data: bytes):
        result = cls()
        glob_path = path.with_suffix(".glob")
        if not glob_path.is_file():
            return result
        lines = glob_path.read_text().splitlines()
        if not lines or lines[0] != "DIGEST " + hashlib.md5(data).hexdigest():
            return result
        result.valid = True
        for line in lines[1:]:
            if line.startswith("F"):
                result.module = line[1:]
            else:
                match = re.fullmatch(r"R(\d+):(\d+) (\S+) (\S+) (\S+) (\S+)", line)
                if match:
                    start, end, module, section, name, kind = match.groups()
                    qualified = ".".join(x for x in (module, section, name) if x != "<>")
                    result.references[int(start)] = (int(end) + 1, qualified, kind)
                    continue
                match = re.fullmatch(r"(\S+) (\d+):(\d+) (\S+) (\S+)", line)
                if match:
                    kind, start, end, section, name = match.groups()
                    qualified = ".".join(x for x in (result.module, section, name) if x != "<>")
                    # Rocq records generated induction schemes at their parent
                    # inductive's offset. Preserve the actual declaration there.
                    result.definitions.setdefault(int(start), (qualified, kind))
        return result


@dataclass
class Source:
    path: Path
    root: Path
    text: str
    module: str
    glob: Glob
    declarations: list = field(default_factory=list)
    errors: list[str] = field(default_factory=list)
    resolution_status: dict[int, str] = field(default_factory=dict)
    arrow_sorts: dict[int, str] = field(default_factory=dict)

    @classmethod
    def load(cls, path, root):
        data = path.read_bytes()
        config = configuration(path, root)
        glob = Glob.load(path, data)
        if glob.valid:
            recorded = path.with_suffix(".glob").stat().st_mtime_ns
            stale = config.is_file() and config.stat().st_mtime_ns > recorded
            imports = {identity for _, identity, kind in glob.references.values() if kind == "lib"}
            # A source digest alone does not detect changed project imports.
            # Reject their old resolution data when a dependency was rebuilt.
            for candidate in discover(root, root / ".rocq-readable-unused-output"):
                if module_name(candidate, configuration(candidate, root), root) in imports:
                    compiled = candidate.with_suffix(".vo")
                    if not compiled.is_file() or compiled.stat().st_mtime_ns > recorded:
                        stale = True
                        break
            if stale:
                glob = Glob()
        return cls(path, root, data.decode("utf-8"), glob.module or module_name(path, config, root), glob)

    @property
    def relative(self):
        return self.path.relative_to(self.root)

    def fragment(self, node):
        loc = node.get("loc") if isinstance(node, dict) else None
        if loc:
            return self.text.encode()[loc["bp"]:loc["ep"]].decode("utf-8")
        return ""

    def range_text(self, range_):
        lines = self.text.splitlines(keepends=True)
        def offset(point):
            # LSP columns count UTF-16 code units, not Python characters.
            line = lines[point["line"]] if point["line"] < len(lines) else ""
            prefix = line.encode("utf-16-le")[:2 * point["character"]].decode("utf-16-le")
            return sum(len(s) for s in lines[:point["line"]]) + len(prefix)
        return self.text[offset(range_["start"]):offset(range_["end"])]
