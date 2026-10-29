# cjr-core

CJR semantics, Iris logic, generic source layer, extraction printers, shared tools, misc and introductory generics. rocq_readable and all its resources live only here.

Open [HTML documentation](docs/index.html) or the [tutorial PDF](paper/tutorial.pdf).

## Setup

Use Python 3.10+, Cangjie 1.0.5, and pdfLaTeX. Proof work additionally needs Coq 8.20.1, stdpp 1.12.0, Iris 4.4.0 and coq-lsp 0.2.5+8.20 for readable specification regeneration. `CJC`, `CANGJIE_HOME`, and `SDKROOT` override the native toolchain.

Dependencies are pinned in dependencies.lock.json. Place checkouts alongside this repository or set `CJR_CORE_DIR` and `CJR_COLLECTIONS_DIR`. `make dependencies` checks versions and generates Rocq load paths. No remote repositories have been created.

## Commands

- `make test`: compile and test checked-in Cangjie, without proof builds.
- `make benchmark`: collect fresh runtime samples, validate checksums, and create charts and HTML.
- `make docs` or `make report`: assemble offline documentation without checking proofs or rerunning benchmarks.
- `make paper`: refresh the benchmark chapter and compile the tutorial PDF twice.
- `make build`: compile this repository's proofs and required dependencies.
- `make extract`: explicitly build proofs and regenerate Cangjie.
- `make verify`: proof checking and the local assumption audit, with build/verify.log.
- `make readable`: regenerate specification HTML using rocq_readable in core; this invokes the proof backend.

Use `ARGS="--example NAME"` to restrict runtime tests or benchmarks. Examples without a benchmark harness are included in runtime tests but have no timing claim. Historical benchmark runs retain original dates and hashes under benchmark/history; current measurements live under benchmark/results.

## Verification status

Proofs were not revalidated during the repository split. Checked-in proof reports and build/verify.log are historical evidence. Current runtime validation is recorded separately in build/runtime-validation.json. Native tests do not establish proof validity or correctness of the extraction printer or compiler. Existing authenticator frontend proof gates remain enforced.
