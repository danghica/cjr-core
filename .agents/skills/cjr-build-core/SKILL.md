---
name: cjr-build-core
description: Build a CJR application core from a cjr-spec-core plan, producing Iris specifications, a CJR implementation, Rocq correctness proofs, extracted Cangjie, a command line interface with HTML reference and architecture diagram, executed tests and benchmarks, and technical documentation under work. Use when a contributor asks to implement a planned CJR core.
---

# Build a CJR application core

Implement the plan produced by `cjr-spec-core` and deliver the artifacts below.
This skill authorizes the build workflow when invoked for a plan; authoring or
editing this skill does not itself start an application build.

## Read the plan and prepare the workspace

Read the accepted core prompt, all appended algebraic validation properties,
and the plan from `cjr-spec-core`, using supplied files or conversation context.
If these inputs are missing or ambiguous, ask the user to identify them; do not
invent a plan or infer acceptance from an unrelated project. Preserve the
hexagonal boundary: the application core contains business logic without
explicit system interactions. Test and benchmark harnesses may perform the
system interactions needed to execute and measure the core.

Read the target repository's `AGENTS.md`, setup instructions, pinned
dependencies, relevant CJR semantics and Iris laws, existing proof examples,
extraction printers, and `tools/rocq_readable/README.md`. Reuse the repository's
actual interfaces and supported CJR fragment. Resolve specification conflicts
or unsupported requirements with the user rather than silently weakening the
plan, changing its architecture, or replacing verified code with native code.

Work relative to the target repository root. Create or reuse these directories
without deleting existing work:

- `work/prompts/`: the accepted prompt, appended properties, and input plan.
- `work/specs/`: CJR Iris specifications, the CJR implementation encoded in
  Rocq, Rocq proofs, extraction drivers, and local proof-build configuration and
  verification records.
- `work/code/`: Cangjie code extracted from that implementation.
- `work/code/test/`: test and benchmark sources, runners, execution logs, raw
  benchmark samples, and result summaries.
- `work/docs/`: generated rocq-readable HTML and the project documentation.
- `work/CLI/`: CLI adapter and bridge sources and reproducible build commands.
- `work/CLI/bin/`: the built CLI executable.
- `work/CLI/doc/`: the CLI HTML reference and hexagonal architecture diagram.

Preserve the accepted inputs as `work/prompts/prompt.md` and
`work/prompts/plan.md` unless the project already has named input files there.
Keep the user's wording and identify appended properties. If existing files
belong to a different project, resolve the target with the user before
overwriting them. If prerequisites are missing, use `cjr-setup` when available
to complete setup within the requested build's scope, or identify the exact
missing dependencies.

## Specify, implement, and prove in work/specs

Define the domain model, operations, admissible inputs, error behavior, state
and ownership invariants, and Iris contracts specified by the plan. Encode the
implementation in CJR using the established Rocq syntax or generic source
layer, rather than writing only a separate native Cangjie implementation.

Prove that the CJR implementation meets its Iris specification. Formalize and
prove the supplied algebraic properties of the specification as separate laws
where needed; an implementation proof alone does not validate the specification
against those laws. Preserve the plan's preconditions and make machine-integer
bounds, representation assumptions, and extraction trust boundaries explicit.

Place the new `.v` sources and local build configuration in `work/specs`.
Configure explicit load paths to the core theories, extraction support, and
the workspace modules. Inspect the current build adapters before choosing
commands: the existing root `make verify` discovers modules under fixed
directories and does not automatically verify sources under `work/specs`.
Use a workspace-local build/verification runner that includes every new module;
keep reproducible commands and logs in `work/specs`. Reuse dependencies without
modifying existing examples merely to make the workspace discoverable.

Compile all new modules with the pinned Coq/Rocq version, kernel-check them
with `coqchk`, and run `Print Assumptions` for the public correctness and
algebraic-validation theorems. Inspect their transitive assumptions. Reject
admissions, aborted proofs, and new axioms used to bypass obligations. Save
the actual commands, exit statuses, tool versions, and source fingerprints in
the verification record. A successful check of the library alone is not a
successful check of the new core. If a proof cannot be completed, report the
remaining obligation and do not describe the core as verified.

## Extract Cangjie into work/code

Use the existing CJR extraction printers on the proved implementation. Put any
workspace extraction driver in `work/specs` and the generated `.cj` files in
`work/code`. The example extraction runner writes to fixed example directories;
inspect and adapt its mechanism for these workspace paths rather than assuming
`make extract` includes the new modules.

Check the emitted inventory, reject unsupported extraction forms, and compile
the extracted code with the required Cangjie SDK. Do not hand-edit the generated
implementation to fix a mismatch: correct its CJR source or extraction support,
then re-prove and re-extract affected artifacts. Record the source-to-generated
file mapping and the extraction commands for reproduction.

## Build the command line interface in work/CLI

Create a runnable CLI for the extracted core, storing its sources and build
instructions in `work/CLI` and its executable in `work/CLI/bin`. Use these exact
directory names, including uppercase `CLI` and singular lowercase `doc`.
Build against the extracted Cangjie implementation; do not duplicate its
business logic in the CLI.

Inventory every top-level application-core function and give each an
appropriately named command. Map the function arguments to documented command
arguments, preserving their names, ordering where relevant, types, and domain
constraints. Include every such function, not just a convenient subset;
proof lemmas, extraction helpers, and the CLI entry point are not application
commands. Record a clear function-to-command mapping, and resolve collisions
with the reserved `help` command without hiding a core function.

Implement argument parsing, validation, and translation to the extracted
representations in an explicit bridge between the CLI adapter and the core's
function interface. Specify encodings for structured values, state, and outputs
so commands can actually invoke the corresponding functions. Keep terminal I/O
and any other explicit system interactions outside the pure core. Do not add
persistence or external services merely to make the CLI stateful; use the
accepted plan's state model and clarify any unresolved requirements.

Provide a command named `help` that lists all available commands, including
`help` itself. For each command, document its arguments and accepted formats,
outputs, and side-effects. Distinguish domain-state changes from external
effects such as standard output or standard error, and explicitly state when
there are no other side-effects. Include invocation examples and error/exit
behavior. Malformed arguments must produce a useful error and a nonzero exit
status without invoking the core with invalid inputs.

Create `work/CLI/doc/index.html` documenting the same command inventory,
arguments, outputs, side-effects, examples, and error behavior as `help`.
Keep both references consistent with the actual function signatures and
executable, preferably using a shared command description. Include an offline
diagrammatic rendering of the project's hexagonal architecture in this HTML:

- Identify the pure application core and its boundary.
- Identify the bridge that translates CLI values and results.
- Identify the ports (the actual core function interfaces) and adapters
  (including the CLI and its terminal interaction).
- Label the connections so readers can trace command input through the adapter,
  bridge, and ports into the core and follow results back to terminal output.

Use an embedded SVG or another locally rendered diagram that works when the
HTML is opened offline. Show the components actually implemented; do not invent
a database, service, or outbound port absent from the project. Explain the
bridge's representation conversions and trust boundary: the core's Rocq proofs
do not automatically verify the CLI or bridge.

## Create and run tests and benchmarks in work/code/test

Create runnable tests against the extracted code, covering the plan's observable
behavior, boundary and error cases, and representative checks of the supplied
algebraic laws. Use a reference model or independently determined expected
results where appropriate. Runtime tests supplement the proofs.

Add and run CLI integration tests against the executable in `work/CLI/bin`.
Cover command/function completeness, argument conversion, representative
function results, malformed arguments, exit statuses, and the `help` command.
Verify that the help and HTML references describe the implemented commands and
their effects consistently. Keep these tests and their results in
`work/code/test` with the other harnesses. Benchmark the core separately from
CLI process startup and parsing, identifying any separately measured CLI cost.

Create and execute a benchmark harness for relevant core operations and input
sizes. Validate results or checksums so the measured computation cannot simply
be discarded. Use warmups and repeated measured runs; retain raw samples,
units, summary statistics, input sizes, compiler flags, versions, execution
time, and machine details. Describe what was actually measured. Do not invent
timings, imply an unmeasured speedup, or treat historical runs as fresh results.

Store harnesses, commands or runners, logs, and results in `work/code/test`.
Run them with the extracted files from `work/code`, using the SDK environment
and paths established during setup. Preserve failures and their exit statuses;
fix failures and rerun affected checks before declaring success.

## Generate HTML in work/docs

Run rocq-readable against the workspace `.v` sources using the same load paths
and compiled proof environment. Inspect its current CLI and project-discovery
rules before invoking it. A typical source selection from the repository root
is `./rocq-readable build --sources work/specs --output work/docs
--explanations offline`, with the actual project configuration/load paths
provided as required by the current renderer. Do not silently render a
different example or the library instead of the new core.

Keep the generated index, declaration pages, styles, dependency information,
and renderer report in `work/docs`. Inspect reported errors and unsupported
forms, and check local links. Report any rendering limitations separately from
proof verification: generating readable HTML is not proof checking.

## Write the project documentation

Write `work/docs/project.md` in readable, technical, concise prose with these
four sections, in this order:

1. **prompt**: reproduce the accepted prompt and appended properties, and link
   to the input plan. Identify the hexagonal boundary and agreed scope.
2. **specifications**: explain the domain model, Iris contracts, algebraic laws,
   and correctness results. Link to the Rocq sources, verification records, and
   rendered HTML. State relevant preconditions and trust boundaries.
3. **code**: explain the CJR implementation and extracted Cangjie, their
   relationship, and reproducible build and extraction commands. Explain how to
   build and run the CLI, its command/function mapping, and the bridge and
   hexagonal boundary. Link to the executable, CLI HTML reference and diagram,
   and relevant source files.
4. **benchmarks and tests**: explain what was tested and measured, how to rerun
   the harnesses, the actual outcomes, and the benchmark environment and units.
   Link to raw samples, summaries, and execution logs; identify any failures or
   incomplete checks.

Use relative links that work from `work/docs/project.md`. Ensure the Markdown
and generated HTML coexist; do not replace the renderer's index with prose.
Do not generate a PDF unless requested separately.

Finish by presenting links to the documentation, specification/proof sources,
extracted code, CLI executable and HTML reference, and test/benchmark results.
Confirm the CLI documentation and diagram render offline and their local links
resolve. State which checks actually passed
and any remaining blockers. Completion requires all requested artifacts and
executed verification, tests, benchmarks, and rendering; partial output must
be identified as partial. Do not commit or push unless asked.
