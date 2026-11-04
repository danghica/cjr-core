---
name: cjr-setup
description: Set up a fresh cjr-core clone by creating its working directories, installing missing proof, Cangjie, documentation, and test dependencies, and checking the resulting environment. Use when a contributor asks to set up, bootstrap, or install dependencies for a CJR repository.
---

# Set up CJR

Complete the installation, rather than only listing commands. Reuse compatible
tools and install missing requirements. A clone does not execute this skill:
activate it when the contributor asks for setup, including `$cjr-setup`.

## Establish the requirements

Locate the checkout from this skill's location, not a developer-specific path.
Read its `AGENTS.md`, `README.md`, `coq-cjr.opam`, `pyproject.toml`, and
`dependencies.lock.json`. Check build adapters under `tools/project_tools/` and
the readable exporter under `tools/rocq_readable/` for additional requirements.
Use the checked-out revision's requirements if they change from the baseline
below. The opam manifest's broad Coq range does not supersede the README's tested
version or the exporter's Coq 8.20 restriction.

The current complete development environment needs:

- Git, GNU Make, Python 3.10+ with venv/pip support, a C/C++ compiler, and opam.
- Coq 8.20.1 (the proof assistant now called Rocq), stdpp 1.12.0, and Iris 4.4.0.
  CJR has no Lean dependency; do not substitute Lean for Coq.
- coq-lsp `0.2.5+8.20`, an OCaml native compiler, ocamlfind, and yojson for
  readable specifications. Opam resolves their transitive dependencies.
- Cangjie SDK 1.0.5, including its runtime libraries and native toolchain.
- pdfLaTeX, `kpsewhich`, and the packages used by `paper/tutorial.tex`, including
  geometry, amsmath, amssymb, amsthm, mathtools, listings, microtype, graphicx,
  float, longtable, TikZ, and hyperref.
- Node.js for the dependency-diagram behavior tests; no npm install is needed.
  Python runtime code uses the standard library; setuptools is needed for an
  optional editable installation of the `rocq-readable` command.

Inspect OS, CPU architecture, available executables, installed versions, opam
switches, and existing `CJC`, `CANGJIE_HOME`, `SDKROOT`, and opam settings before
installing. Respect existing explicit overrides.

## Create the working directories

From the target repository root, create a `work` directory containing `prompts`,
`specs`, `code`, `docs`, and `pdf`:

```sh
mkdir -p work/prompts work/specs work/code work/docs work/pdf
```

Create these directories even if dependency installation is blocked. Reuse
existing directories and preserve their contents on subsequent runs. If any
required path is occupied by a file, report that conflict without replacing it.
Confirm all five paths are directories before reporting this step as complete.

## Install the missing tools

Use the host's package manager and the vendors' official installation sources.
Install only missing system packages. On macOS, check the Xcode Command Line
Tools with `xcrun --show-sdk-path`; on Linux, ensure the compiler, linker, and SDK
prerequisites specified by Cangjie are installed. For Debian/Ubuntu, a typical
base is `git make build-essential python3 python3-venv python3-pip opam pkg-config
curl unzip rsync m4 nodejs`; TeX typically needs `texlive-latex-recommended`,
`texlive-latex-extra`, `texlive-pictures`, and `texlive-fonts-recommended`.
On macOS, reuse Homebrew or MacPorts if present and install a TeX distribution
such as BasicTeX with the missing packages, or MacTeX. Determine package names
for other distributions from their own documentation.

Install user-scoped tools without elevated privileges when possible. Proceed
under the contributor's setup request; request intervention only for actual
password dialogs, permissions, licenses, incompatible existing environments, or
unsupported platforms. Do not remove or downgrade unrelated installations.

### Proof environment

Important: current build adapters prepend `~/.opam/default/bin`, and the
verification audit invokes tools at that path directly. Merely activating a
different switch does not configure the whole project. Inspect this behavior
in the current revision before choosing a switch.

For a new opam installation, initialize without changing shell startup files:

```sh
opam init --bare --no-setup -y
opam switch create default ocaml-base-compiler.4.14.2 -y
```

Run these only when the opam root or default switch, respectively, is absent.
OCaml 4.14.2 is a compatible bootstrap choice, not an additional project pin.
Reuse an existing compatible compiler. If a populated default switch would
need incompatible changes, explain the concrete conflict before changing it;
continue installing independent missing requirements meanwhile. Do not silently
replace it or claim a separate switch works with hardcoded paths.

Add the released Rocq package repository to the default switch if it has no
equivalent repository, then install the pinned proof packages:

```sh
opam repository add rocq-released https://rocq-prover.org/opam/released --switch=default
opam update
opam install --switch=default -y coq.8.20.1 coq-stdpp.1.12.0 coq-iris.4.4.0 'coq-lsp.0.2.5+8.20' ocamlfind yojson
```

Inspect the solver's proposed changes for an existing switch before applying
them. Activate it for subsequent commands with `eval "$(opam env
--switch=default --set-switch)"` in a single shell line, or use `opam exec
--switch=default -- COMMAND`. Confirm actual package versions with `opam list
--switch=default --installed`; `coq-lsp --version` alone omits its Coq suffix.

### Cangjie and local environment

Obtain SDK **1.0.5** for the actual OS and architecture from the
[official versioned download page](https://cangjie-lang.cn/download/1.0.5),
following its installation guide and checking its published checksum. Do not
guess download URLs or substitute the latest SDK. Install into a user-owned
directory and source the SDK environment script as directed by its guide.
If the archive requires a manual download or license interaction, identify the
exact remaining step and continue with other installation work.

Set `CJC` to the absolute installed `bin/cjc` path and `CANGJIE_HOME` to its SDK
root. The runtime test adapter otherwise defaults to a developer-specific path
under `~/cangjiebuild/`; having `cjc` on PATH alone is insufficient. Preserve the
SDK's platform-specific runtime library settings. The adapter currently sets a
macOS ARM runtime path itself: on Linux, investigate any resulting runtime
failure and report it as a portability issue rather than claiming successful
setup or installing an SDK for another architecture.

For persistent project activation, create an untracked `.cjr-env.sh` with the
actual opam/SDK activation commands and exports, and add its exact filename to
`.git/info/exclude` (resolve this with `git rev-parse --git-path info/exclude`
for worktrees). Do not commit machine-specific paths or change global shell
startup files. If the file exists, preserve unrelated content. Tell the
contributor to run `. ./.cjr-env.sh` in future shells.

Run Python tools directly from the checkout. If the contributor wants the
installed CLI, create an ignored `.venv`, activate it, and use `python -m pip
install -e .`; never install into system Python. The standalone `./rocq-readable`
launcher needs no editable installation.

For sibling CJR repositories, read their own lock files and fetch missing
dependencies at the recorded commits into new sibling checkouts, or use
`CJR_CORE_DIR` / `CJR_COLLECTIONS_DIR` overrides. Never reset an existing dirty
checkout. Core's current empty lock file requires no sibling repositories.

## Verify the installation

Run checks in the installed environment from the repository root:

1. Check Python, `cjc --version`, `coqc --version`, installed opam package
   versions, `coq-lsp --version`, `ocamlopt -version`, and `node --version`.
   Use `kpsewhich` to confirm the tutorial's `.cls`/`.sty` files are present.
2. Run `make dependencies` and `make readable-plugin`.
3. Run `make verify` and `make test`. Preserve the generated verification log
   and actual exit status. Do not run `make extract` just to check setup.
4. Run `python3 -m unittest discover -s tests`. Distinguish tool-related skips
   from passing tests; missing installed dependencies must not be hidden by skips.
5. Smoke-test the readable backend with `./rocq-readable render
   example/misc/rocq/swap.v --name swap_wp --explanations offline --output
   /tmp/cjr-setup-swap.html`, using a fresh temporary directory instead of a
   shared filename when executing. This avoids regenerating all checked-in docs
   or requiring an LLM/API key.
6. Compile the tutorial twice using pdfLaTeX from the repository root with
   `-interaction=nonstopmode -halt-on-error -output-directory=TEMP_DIRECTORY`.
   Use a fresh temporary output directory to preserve the checked-in PDF and
   existing benchmark evidence.

Report the created/reused working directories, installed/reused versions, how to
activate the environment, and which
checks passed, failed, or remain blocked. A network, platform, or permission
failure is an incomplete setup, not permission to relax dependency pins or skip
verification silently. Installation is repeatable: a second run should reuse
the working tools. Do not commit or push unless asked.

Official installation references:
[opam](https://opam.ocaml.org/doc/Install.html),
[Rocq packages](https://rocq-prover.org/docs/using-opam), and
[the pinned coq-lsp package](https://opam.ocaml.org/packages/coq-lsp/coq-lsp.0.2.5%2B8.20/).
