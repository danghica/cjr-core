# Shared project tools

`benchmark.py` runs project-configured Cangjie benchmark jobs, parses their
machine-readable output, writes normalized `raw.csv`, medians/IQR in
`summary.json`, compiler and source provenance in `metadata.json`, local SVG
charts, and a static HTML report. The suite configuration owns only compiler
arguments, harness inputs, output parsing, workload labels, and protocol
description. Run it from the repository root:

```sh
python3 tools/project_tools/benchmark.py run path/to/benchmark.config.json
python3 tools/project_tools/benchmark.py plot path/to/benchmark.config.json
python3 tools/project_tools/benchmark.py report path/to/benchmark.config.json
```

Configuration paths are relative to the `project_root` value (the directory
containing the config by default). The runner accepts `CJC`, `CANGJIE_HOME`,
and `SDKROOT` environment overrides and rejects source or output paths outside
that project boundary. Set `provenance_root` relative to `project_root` when
the report belongs to a nested example; source hashes then use that example’s
paths while compilation still resolves against the build root.

`docs.py` builds source metadata, generic test-report pages, a project report
index from the declaration navigation emitted by `rocq-readable`, and checks
all generated HTML links and fragments:

```sh
python3 tools/project_tools/docs.py metadata path/to/project.config.json
python3 tools/project_tools/docs.py test-report path/to/project.config.json
python3 tools/project_tools/docs.py report path/to/project.config.json
```

An example config supplies its output paths, declaration-group patterns,
artifact labels, and short project description. Its proofs, extracted source,
test cases, benchmark harnesses, and workload definitions stay with that
example. All generated report pages and assets are static and work offline.

`support.py` shares compiler selection and source-provenance helpers used by
project-instance test, verification, and extraction adapters.

## Example dispatch

Examples and their artifacts live under `example/<name>/`. Run `python3 -m tools.project_tools.examples readable --explanations offline`, `test`, or `report` from the repository root; `--example <name>` limits the action. The `benchmark` command explicitly collects new timings; `report` only redraws saved measurements. Shared extraction code is in `tools/extraction/rocq/`, and the benchmark timing helper is `tools/project_tools/benchmark_common.cj`. Historical mixed-suite records are in `paper/benchmark-history/` and `paper/test-history.md`; they retain their original provenance.

A benchmark config may set `plots.command` to an argv list (with `{root}` and
`{output}` placeholders) for example-specific charts. The command runs with the
project working directory and must succeed before report assembly continues.

## Chart semantics and manuscript outputs

The default SVG renderer uses a shared time axis within each facet. Each row
identifies a workload and input size; colored dots encode the measured median,
and whisker endpoints encode Q1 and Q3 on that same axis. Lower values are
faster. Labels show ns/op; the harness defines what counts as an operation.
The October 16 fix replaced a layout whose dots ignored the median. Existing
raw samples, numerical summaries, and measurement metadata remain unchanged.

`python3 paper/update_benchmarks.py` (with ReportLab installed) regenerates the
PDF manuscript figures and LaTeX table from the saved list, array, array-list,
and hash-map runs. Ratios are computed from CJR/Std samples paired by process
and trial, then summarized; they need not equal the ratio of individual medians.
`make cj` rebuilds the tutorial PDF. `make project-report EXPLANATIONS=offline REPORT_FLAGS=--allow-stale`
refreshes readable specifications and all offline HTML reports without new timings.

Report assembly remains strict by default: source mismatches fail. For a
documentation-only refresh, `report --allow-stale` explicitly permits saved
snapshots and adds a prominent source-mismatch notice to the project index.
The switch never rewrites recorded hashes or dates and still rejects failed
checks. With Make, use `REPORT_FLAGS=--allow-stale` as shown above.

The shared readable build excludes `theories/verify_assumptions.v`: it contains
only audit commands and contributes no declaration pages. `make verify` still
runs that audit; documentation rendering does not need to repeat it through
coq-lsp.
