"""Configuration-driven Cangjie benchmark runner and result normalizer.

Each example owns only its harness and a JSON description of compile/run jobs.
The runner, CSV schema, summaries, metadata, and basic SVG chart are shared.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import html
import json
import os
import platform
import re
import shlex
import shutil
import statistics
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.project_tools.docs import hashes as project_hashes
NUMERIC = {"n", "trial", "process", "repetitions", "elapsed_ns", "operations", "checksum"}
BASE_COLUMNS = ["case", "distribution", "n", "workload", "implementation", "process",
                "trial", "repetitions", "elapsed_ns", "operations", "checksum",
                "ns_per_operation"]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_config(path: Path):
    config = json.loads(path.read_text())
    root = (path.parent / config.get("project_root", ".")).resolve()
    return config, root


def provenance_root(config, root: Path) -> Path:
    """Scope source hashes to the report project while retaining build paths."""
    candidate = (root / config.get("provenance_root", ".")).resolve()
    if not candidate.is_relative_to(root.resolve()):
        raise ValueError("benchmark provenance root must stay inside its project root")
    return candidate


def render(value, values):
    if isinstance(value, str):
        return value.format_map({k: str(v) for k, v in values.items()})
    if isinstance(value, list):
        return [render(v, values) for v in value]
    if isinstance(value, dict):
        return {k: render(v, values) for k, v in value.items()}
    return value


def normalize(job, raw, process):
    row = {key: value for key, value in job.get("dimensions", {}).items()}
    fields = job.get("fields", {key: key for key in raw})
    row.update({key: raw[group] for key, group in fields.items()})
    row.setdefault("case", job["name"])
    row["process"] = process
    for key in NUMERIC:
        if key in row and row[key] is not None:
            row[key] = int(row[key])
    if "elapsed_ns" not in row:
        raise ValueError(f"{job['name']}: fields must map elapsed_ns")
    row.setdefault("operations", None)
    row.setdefault("repetitions", None)
    denominator = row["operations"] or row["repetitions"]
    row["ns_per_operation"] = row["elapsed_ns"] / denominator if denominator else None
    for col in BASE_COLUMNS:
        row.setdefault(col, None)
    return row


def run(config_path: Path):
    config, root = load_config(config_path)
    output = (root / config.get("output", "benchmark/results")).resolve()
    if not output.is_relative_to(root):
        raise ValueError("benchmark output must stay inside its project root")
    output.mkdir(parents=True, exist_ok=True)
    cjc = os.environ.get("CJC", config.get("compiler", "cjc"))
    cjc = shutil.which(cjc) or (cjc if Path(cjc).is_file() else "")
    if not cjc:
        candidate=Path.home()/"cangjiebuild/software/cangjie/bin/cjc"
        if candidate.is_file(): cjc=str(candidate)
        else: raise FileNotFoundError("Set CJC to the Cangjie compiler executable")
    environment = os.environ.copy()
    sdk = os.environ.get("SDKROOT", config.get("sdkroot"))
    compiler_home = os.environ.get("CANGJIE_HOME")
    if not compiler_home and Path(cjc).exists():
        compiler_home = str(Path(cjc).resolve().parent.parent)
    if compiler_home:
        environment["CANGJIE_HOME"] = compiler_home
        environment.setdefault("DYLD_LIBRARY_PATH", str(Path(compiler_home) / "runtime/lib/darwin_aarch64_cjnative"))
    if sdk:
        environment["SDKROOT"] = sdk
    elif platform.system() == "Darwin":
        sdk_path=Path(subprocess.check_output(["xcrun","--show-sdk-path"],text=True).strip())
        compat=Path(tempfile.gettempdir())/"cjr-project-sdk"
        for stub in (sdk_path/"usr/lib").rglob("*.tbd"):
            if stub.is_symlink(): continue
            target=compat/stub.relative_to(sdk_path);target.parent.mkdir(parents=True,exist_ok=True)
            contents=re.sub(r"arm64e\.x1-[\w]+\s*,?\s*", "", stub.read_text())
            contents=re.sub(r",\s*\]", " ]", contents).replace("arm64e-", "arm64-")
            if not target.exists() or target.read_text()!=contents: target.write_text(contents)
        link=compat/"usr/lib/libSystem.tbd"
        if not link.is_symlink(): link.symlink_to("libSystem.B.tbd")
        environment["SDKROOT"]=str(compat)
        sdk=str(compat)
    version = subprocess.check_output([cjc, "--version"], cwd=root, env=environment, text=True).strip()
    required=config.get("required_compiler_version")
    if required and required not in version:
        raise RuntimeError(f"{required} required; compiler reports {version}")
    rows = []
    source_hashes = {}
    harness_hashes = {}
    jobs = config["jobs"]
    processes = int(config.get("processes", 3))
    timeout = int(config.get("timeout_seconds", 900))
    with tempfile.TemporaryDirectory(prefix="project-benchmark-") as scratch:
        for job in jobs:
            job_root = root
            name = job["name"]
            core = Path(os.environ.get('CJR_CORE_DIR', ROOT)).resolve()
            source_vars = {'core': core, 'root': root}
            resolve_source = lambda p: (root / render(p, source_vars)).resolve()
            sources = [resolve_source(p) for p in job["sources"]]
            for path, rel in zip(sources, job["sources"]):
                if not path.is_file() or not (path.resolve().is_relative_to(root) or path.resolve().is_relative_to(core)):
                    raise ValueError(f"missing or out-of-project benchmark source: {rel}")
                source_hashes[rel] = digest(path)
            binary = str(Path(scratch) / name)
            variables = {"root": str(root), "output": str(output), "binary": binary,
                         "cjc": cjc, "name": name, "core": core}
            compile_argv = render(job["compile"], variables)
            compile_env = environment | render(job.get("compile_env", {}), variables)
            compile_result = subprocess.run(compile_argv, cwd=root, env=compile_env,
                                             text=True, capture_output=True, timeout=timeout)
            (output / f"{name}.compile.log").write_text(compile_result.stdout + compile_result.stderr)
            if compile_result.returncode:
                raise subprocess.CalledProcessError(compile_result.returncode, compile_argv,
                                                    compile_result.stdout, compile_result.stderr)
            for process in range(processes):
                variables.update(process=process)
                run_argv = render(job["run"], variables)
                run_env = environment | render(job.get("run_env", {}), variables)
                result = subprocess.run(run_argv, cwd=root, env=run_env, text=True,
                                        capture_output=True, timeout=timeout)
                suffix = f".run{process}.log"
                (output / f"{name}{suffix}").write_text(result.stdout + result.stderr)
                if result.returncode:
                    raise subprocess.CalledProcessError(result.returncode, run_argv,
                                                        result.stdout, result.stderr)
                matches = list(re.finditer(job["pattern"], result.stdout))
                expected = job.get("expected_rows_per_process")
                if expected is not None and len(matches) != int(expected):
                    raise RuntimeError(f"{name} process {process}: expected {expected} rows, got {len(matches)}")
                harness_hashes.update({p: digest(resolve_source(p)) for p in job.get("harness_sources", [])})
                for match in matches:
                    rows.append(normalize(job, match.groupdict(), process))

    if not rows:
        raise RuntimeError("benchmark jobs produced no measurements")
    columns = BASE_COLUMNS + sorted({k for row in rows for k in row} - set(BASE_COLUMNS))
    with (output / "raw.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=columns, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    group_by = config.get("group_by", ["case", "distribution", "n", "workload", "implementation"])
    groups = {}
    for row in rows:
        key = tuple(row.get(k) for k in group_by)
        groups.setdefault(key, []).append(row["ns_per_operation"])
    summary = []
    for key, values in sorted(groups.items(), key=lambda item: tuple(str(x) for x in item[0])):
        quartiles = statistics.quantiles(values, n=4, method="inclusive") if len(values) > 1 else [values[0]] * 3
        item = dict(zip(group_by, key))
        item.update(samples=len(values), median_ns=statistics.median(values),
                    q1_ns=quartiles[0], q3_ns=quartiles[2], iqr_ns=quartiles[2] - quartiles[0])
        summary.append(item)
    (output / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    metadata = {
        "dependency_commits": json.loads((Path(os.environ.get("CJR_PROJECT_ROOT", root))/"dependencies.lock.json").read_text()) if (Path(os.environ.get("CJR_PROJECT_ROOT", root))/"dependencies.lock.json").exists() else {},
        "status": "passed", "date_utc": datetime.now(timezone.utc).isoformat(),
        "compiler": version, "sdk": sdk or environment.get("SDKROOT", "compiler default"),
        "machine": platform.uname()._asdict(), "processes": processes,
        "samples": len(rows), "group_by": group_by,
        "benchmark_sources": source_hashes, "harness_sources": harness_hashes,
        "sources": project_hashes(provenance_root(config, root)), "protocol": config.get("protocol", {}),
    }
    (output / "metadata.json").write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n")
    print(f"Saved {len(rows)} normalized measurements to {output}")


def plot(config_path: Path):
    config, root = load_config(config_path)
    output = (root / config.get("output", "benchmark/results")).resolve()
    if not output.is_relative_to(root):
        raise ValueError("benchmark output must stay inside its project root")
    summary = json.loads((output / "summary.json").read_text())
    plot_config = config.get("plots", {})
    if plot_config.get("command"):
        command = render(plot_config["command"], {"root": root, "output": output})
        subprocess.run(command, cwd=root, check=True, timeout=int(config.get("timeout_seconds", 900)))
        return
    by = plot_config.get("facet", "distribution")
    facets = sorted({str(r.get(by, "all")) for r in summary})
    for facet in facets:
        records = [r for r in summary if str(r.get(by, "all")) == facet]
        implementations = sorted({str(r.get("implementation", "")) for r in records})
        workload_of = lambda r: str(r.get("workload") or r.get("case") or "workload")
        workloads = sorted({workload_of(r) for r in records})
        rows = [(workload, size) for workload in workloads
                for size in sorted({r.get("n") for r in records if workload_of(r) == workload},
                                   key=lambda n: (n is not None, int(n or 0)))]
        row_height = max(76, 30 + 20 * len(implementations))
        width, height = 1040, 100 + len(rows) * row_height
        colors = ["#176f76", "#de8b37", "#8562a0", "#2776a8", "#b24e52"]
        max_value = max(1e-9, max(float(r["q3_ns"]) for r in records))
        time_x = lambda value: 230 + 650 * float(value) / max_value
        parts = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" role="img">',
                 f'<title>{html.escape(facet)} benchmark medians and IQR</title>',
                 '<style>text{font:12px system-ui;fill:#26333a}.axis{stroke:#9aa7aa}.grid{stroke:#e4e9e9}</style>',
                 '<rect width="100%" height="100%" fill="white"/>',
                 f'<text x="20" y="24" font-size="17">{html.escape(facet)} · median and IQR</text>']
        for i, impl in enumerate(implementations):
            color = colors[i % len(colors)]
            parts.append(f'<circle cx="{250+i*150}" cy="44" r="5" fill="{color}"/><text x="{260+i*150}" y="48">{html.escape(impl)}</text>')
        bottom = 65 + len(rows) * row_height
        for tick in range(5):
            value = max_value * tick / 4
            x = time_x(value)
            parts.append(f'<path d="M {x:.1f} 65 V {bottom}" class="grid"/><text x="{x:.1f}" y="{bottom+18}" text-anchor="middle">{value:.2f}</text>')
        parts.append(f'<text x="555" y="{bottom+36}" text-anchor="middle">Time (ns per operation; lower is faster)</text>')
        for ri, (workload, size) in enumerate(rows):
            y = 80 + ri * row_height
            label = workload if size is None else f"{workload} · n={int(size):,}"
            parts.append(f'<text x="18" y="{y}">{html.escape(label)}</text>')
            for ii, impl in enumerate(implementations):
                values = [r for r in records if workload_of(r) == workload
                          and r.get("n") == size and str(r.get("implementation", "")) == impl]
                for r in values:
                    mid = y + 10 + ii * 20
                    lo, median, hi = (time_x(r[key]) for key in ("q1_ns", "median_ns", "q3_ns"))
                    color = colors[ii % len(colors)]
                    description = html.escape(f"{impl}: median {r['median_ns']:.4f}, Q1 {r['q1_ns']:.4f}, Q3 {r['q3_ns']:.4f} ns/op")
                    parts.append(f'<g><title>{description}</title><path d="M {lo:.1f} {mid} H {hi:.1f}" stroke="{color}" stroke-width="2"/><circle cx="{median:.1f}" cy="{mid}" r="4" fill="{color}"/><text x="900" y="{mid+4}">{html.escape(impl)} {r["median_ns"]:.2f} ns/op</text></g>')
        parts.append('</svg>')
        filename = plot_config.get("filename", "{facet}.svg").format(facet=facet.lower().replace(" ", "-").replace("/", "-"))
        (output / filename).write_text("\n".join(parts) + "\n")


def report(config_path: Path):
    config, root = load_config(config_path)
    output = (root / config.get("output", "benchmark/results")).resolve()
    summary = json.loads((output / "summary.json").read_text())
    metadata = json.loads((output / "metadata.json").read_text())
    columns = config.get("report_columns", [k for k in ("distribution", "n", "workload", "case", "implementation") if any(k in row for row in summary)])
    rows = "".join("<tr>" + "".join(f"<td>{html.escape(str(row.get(k, '')))}</td>" for k in columns) +
                   f"<td>{float(row['median_ns']):.2f}</td><td>{float(row['iqr_ns']):.2f}</td><td>{int(row['samples'])}</td></tr>" for row in summary)
    workload_items = config.get("workloads", {})
    workloads = "<dl>" + "".join(f"<dt>{html.escape(name)}</dt><dd>{html.escape(description)}</dd>" for name, description in workload_items.items()) + "</dl>" if workload_items else ""
    charts = "".join(f'<h2>{html.escape(p.stem.replace("-", " ").title())}</h2><img src="{html.escape(p.name, quote=True)}" alt="Benchmark chart for {html.escape(p.stem)}">'
                     for p in sorted(output.glob("*.svg")))
    header = "".join(f"<th>{html.escape(k.replace('_',' ').title())}</th>" for k in columns)
    body = ("<p>Results are normalized by the shared project benchmark runner. Median and IQR are shown for each configured workload and implementation.</p>" + workloads + charts +
            f'<h2>Measurements</h2><div class="scroll"><table><thead><tr>{header}<th>Median ns/op</th><th>IQR ns/op</th><th>Samples</th></tr></thead><tbody>{rows}</tbody></table></div>' +
            '<h2>Downloads</h2><p><a href="raw.csv">Raw normalized CSV</a> · <a href="summary.json">Summary JSON</a> · <a href="metadata.json">Compiler, machine and source metadata</a></p>' +
            f'<details><summary>Metadata</summary><pre>{html.escape(json.dumps(metadata, indent=2))}</pre></details>')
    if metadata.get("historical"):
        body = '<p>Historical measurements, relocated without rerunning timings. Original run dates and source hashes are preserved in the metadata.</p>' + body
    path = output / "report.html"
    css = config.get("report_css", "../../docs/report.css")
    index = config.get("report_index", "../../index.html")
    path.write_text(f'<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Benchmark report</title><link rel="stylesheet" href="{html.escape(css, quote=True)}"><main><header><h1>Benchmark report</h1><a href="{html.escape(index, quote=True)}">Project index</a></header>{body}</main></html>')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["run", "plot", "report"])
    parser.add_argument("config", type=Path)
    args = parser.parse_args()
    {"run": run, "plot": plot, "report": report}[args.command](args.config.resolve())


if __name__ == "__main__":
    main()
