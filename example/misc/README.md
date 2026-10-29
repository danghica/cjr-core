# misc

All example-specific assets live here. Existing Rocq definitions, specifications, and proofs remain together in `rocq/`, with their original `cjr.examples.*` import names. Generated Cangjie is in `extracted/`, runtime tests in `test/`, and rendered specifications and dependency diagrams in `docs/rocq/`. Existing benchmarks and papers are under `benchmark/` and `docs/`.

Open [the offline report](index.html) or [all examples](../index.html). From this directory run `make build`, `make extract`, `make test`, `make docs`, or `make assemble`. Set `EXPLANATIONS=offline` to reuse explanation caches without model requests. `make benchmark` runs timed measurements only where a harness exists. Shared libraries and sibling examples are resolved through the repository build configuration.

The arithmetic example now includes `multiply` and a checked multiplication
specification. Core multiplication evaluates on unbounded Rocq integers and
prints `Int64` multiplication in Cangjie; its WP rule does not imply a machine
overflow check or a wrapping policy. The native test suite covers multiplication
alongside the existing small examples. The [main tutorial](../../paper/cjr-tutorial.pdf)
and [operator description](../../README.md#integer-and-bitwise-operators) explain
the model-to-machine boundary.
