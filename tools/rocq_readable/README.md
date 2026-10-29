# Rocq Readable

A specification renderer for Coq 8.20.1 and CJR/Iris. Rocq parses the source;
the tool turns the concrete AST into linked, proof-free HTML. Formal rendering
and dictionary rules remain deterministic. Optional English explanations are
generated through the user's authenticated Codex CLI and cached locally.

## Installation and commands

Python 3.10 or newer and `coq-lsp.0.2.5+8.20` are required. Activate the opam
switch with `eval $(opam env)`. If `coq-lsp` is absent from PATH, the CLI also
checks the default opam switch. A different backend release is rejected.

Run `./rocq-readable` from this repository, `python3 -m tools.rocq_readable`,
or install the Python package with `python3 -m pip install .` to obtain the
`rocq-readable` command. The installed command treats its invocation directory
as the project root.

```sh
rocq-readable build --output generated/spec-html
rocq-readable build --output generated/spec-html --strict
rocq-readable render example/misc/rocq/swap.v --name swap_wp --output /tmp/swap.html
rocq-readable build --dictionary ./my-renderings.json --learn
rocq-readable build --explanations offline
rocq-readable build --llm-model YOUR_MODEL --llm-timeout 120
```

`make readable` and `make readable-test` provide repository shortcuts.
Integration tests require the backend; tests report a skip when it is missing.

Whole-project output contains a dependency homepage (`index.html`), a flat
declaration **Index** (`declarations.html`), one page per `.v` file, `style.css`,
and `report.json`. Source pages link to Home and Index. The directory structure
mirrors the source tree; source filenames colliding with navigation pages get
a `.source.html` suffix. Individual
rendering produces a standalone HTML file with embedded CSS and a sibling
`.report.json`; it does not overwrite an unrelated index or stylesheet.

## Dependencies and English explanations

The homepage presents expandable, indented bullets: each entry links to its
rendered declaration, and its children are declarations it depends on. Shared
dependencies appear under every parent. Roots are declarations with no
dependents, isolated declarations, and representatives of otherwise unreachable
cycles. Recursive references stop expansion along that path. Branches expand
lazily using embedded data and local JavaScript; no remote assets are needed.
Each declaration also lists direct dependencies for navigation without JavaScript.

The homepage also includes an offline SVG dependency graph. The source-file
overview groups declarations by file and shows cross-file dependencies. Select
**All declarations** for the complete graph, or search for a declaration to see
its direct dependencies and dependents. Shared declarations appear once in the
diagram; arrowheads point toward dependencies, including recursive links.
Node colors distinguish specifications, algorithms, proofs, and other sources.
Click nodes to open documentation. Drag the background to pan and use the
zoom buttons, mouse wheel, or keyboard controls to explore larger graphs.
Diagram coverage matches the hierarchy, including its resolution notices.

Each source page also begins with a graph of dependencies among its own
declarations and lemmas. Nodes jump to the entries below; search, focused
neighborhoods, pan, and zoom work as on the homepage. Colors distinguish
definitions, lemmas, types, and other declarations. Cross-file dependencies
remain accessible in each entry's dependency list and the project graph.

Dependencies include references in types, bodies, binders, section context, and
hidden proofs. Constructor and field references lead to their containing
declaration. Fresh `.glob` data supplies resolved lexical references; otherwise
the tool resolves explicit references, including tactic references, through LSP.
It never guesses dependencies from short names. Without fresh `.glob` data,
notation and implicit tactic references can be incomplete. Tactics that discover
lemmas implicitly are not a complete proof-term dependency analysis, even with
`.glob` data. Notices and `report.json` describe resolution limits and truncated
or aborted proofs. Standalone rendering still stops before the selected proof
and reports its proof dependencies as incomplete.

Every rendered entry includes an **AI-generated explanation** or an explicit
unavailable notice. `--explanations auto` (the CLI default) uses matching cached
text first, then invokes `codex exec` for missing entries when the CLI is on PATH.
`--explanations offline` uses only the cache and makes no model requests.
The Python `generate()` function defaults to offline operation; pass explanation
options explicitly to enable requests when embedding the renderer.

Codex reuses its saved login and configured model. Each user authenticates on
their own machine; no credentials are read or copied into source, HTML, reports,
or caches. Requests run sequentially in temporary directories with a read-only
sandbox, ephemeral sessions, shell/browser tools, plugins, apps, and hooks disabled,
and approvals disabled. A bounded tail of CLI diagnostics is inspected privately
to recognize sandbox startup failures, then discarded; raw diagnostics are never
included in reports. The prompts contain the
proof-free declaration, rendered text, section context, and direct dependency
declarations. These texts are sent to the model provider under the user's Codex
account. Generated explanations are explanatory prose, not verified translations.

Use `--llm-model MODEL` to select a model explicitly, and `--llm-timeout SECONDS`
to bound each request (default 120). Cache keys include the supplied content,
prompt version, and model selection. Pin the model explicitly if switching CLI
defaults should invalidate existing explanations. Cached output can be reused
offline and unchanged cached builds are deterministic.

The versioned JSON cache defaults to `explanations.json` in the build directory,
or a sibling `.explanations.json` for standalone output. `--explanation-cache PATH`
selects a separate JSON file. Writes are atomic. If you commit a cache, its
explanation text becomes public along with your repository. The cache stores
qualified identities, input hashes, and descriptions, without credentials or
raw CLI diagnostics.

Failed requests, invalid responses, or cache errors are recorded and return
status 1 after pages are generated. Offline cache misses and an absent Codex CLI
are reported omissions rather than failed generation attempts. See the
`dependencies` and `explanations` sections of `report.json` for per-entry status.

An enclosing agent or OS sandbox can prevent the Codex CLI from initializing its
local app-server client before any model request. This is reported as a sandbox
startup failure, and further uncached requests are skipped for that build. Run
the same command from an environment that permits app-server initialization,
with authorization to send the declaration text to Codex. Keep the nested CLI's
read-only sandbox and disabled tools; changing credentials or the model does not
resolve this startup restriction. Offline rendering remains available.

`--name` accepts a short or qualified name. Ambiguous short names are rejected.
Single-declaration rendering stops after the declaration, so its proof can be
absent or invalid. Earlier commands and proofs may still need checking to
establish the declaration's environment.

## Project boundary and links

Discovery walks the current directory recursively, including hidden directories
and unlisted `.v` files. Git metadata, the selected output directory, and
symlinks are excluded. Neither source discovery nor symbol links follow paths
outside this root.

The nearest ancestor `_RocqProject` or `_CoqProject` within the root supplies
backend configuration; `_RocqProject` takes precedence when both exist. These
files configure parsing rather than limit the discovered inventory. Dependencies
must already be available to Rocq; generation does not build or install them.

Compiled `.glob` files provide exact global identities, notation scopes,
constructors, fields, and lexical reference data. They are used only when their
source digest matches and project configuration/import timestamps remain current.
Without a fresh `.glob`, the tool asks coq-lsp for symbol
destinations and leaves ambiguous or unavailable references unlinked. Run the
normal project build for the most complete link coverage. Dictionary renaming
changes display text without changing the destination.

All emitted links are relative and point to generated project declarations or
local binders. Library references and references whose project destination is
not generated remain plain text. An individual page links only to declarations
and binders included in that page. Qualified Rocq identities determine stable,
ASCII declaration anchors.

## Scope and logical fidelity

Four-space indentation determines multiline scope; colons introduce blocks and
dedentation closes them. Multiline calls have no enclosing parentheses. Scope
brackets appear only when the whole expression fits on a single line. Brackets
inside data literals retain their data meaning. HTML preserves whitespace and
scrolls horizontally instead of wrapping lines at narrow screen widths.

The renderer keeps parameters, explicit types, inferred-type holes, implicit
markers, context assumptions, and original declaration names. It distinguishes
ordinary implication, consuming implication, entailment, conjunction, separating
conjunction, pure assertions, persistence, and later modalities. Explicit WP
masks, stuckness arguments, and postcondition binders stay in the document.
Iris WP specifications express partial correctness, not termination.

Ordinary propositional implication renders as `IF A THEN B`; equality renders
as `A=B`. Isolated Rocq `Check` queries establish whether an arrow has sort
`Prop` in its declaration environment, including explicit local binders.
Function types retain `arrow(A, B)`. If a check cannot reconstruct the local
context (for example pattern binders or inferred types), the arrow also retains
that spelling and the coverage report records an unclassified arrow. These
queries do not modify the source or the document's proof state. Consuming
implication remains a separate construct.

Resolved CJR expression/value constructors render recursively as Cangjie surface
syntax: literals, identifiers, calls, operators, `let`/`var`, assignments,
sequences, anonymous closures, `if`/`while`, and unsafe pointer operations.
Literal string identifiers and optional binders receive contextual treatment;
Cangjie keywords use the same renaming as the repository's extraction printer.
Bindings and their uses remain linked. Helper references remain symbolic: the
renderer does not unfold definitions or reconstruct complete programs.
Stack forms, recursive/symbolic closures, symbolic identifiers, and aggregate
operations requiring unavailable layout metadata retain a marked CJR form with
all arguments, and appear in the coverage report. This presentation may contain
symbolic Rocq expressions and is not a standalone compilable Cangjie program.

Built-in rules cover common Gallina/stdlib forms and CJR/Iris ownership and WP
notation. Other functions remain calls. Unmapped notation retains its exact
grammar key and every substitution slot. Unsupported AST forms retain a marked
original-source fragment. Every declaration has an expandable proof-free source
excerpt. Original-source displays retain Rocq syntax and its original brackets.

Rendering does not unfold predicates, simplify terms, erase technical premises,
or certify a user's interpretation. The output is an auditable presentation,
not a formally verified translation or a replacement for proof checking.

## Dictionary and interactive learning

The default version-controlled dictionary is `renderings.json` beside this
document. Use `--dictionary` to select another file; a nonexistent path starts
an empty dictionary. Ordinary rendering never writes the dictionary.

The JSON root has exactly `version: 1` and a `rules` array. Each rule has:

- `kind`: `application` or `notation`.
- `key`: the resolved function identity or exact parsed notation grammar key.
- `arity`: the number of substitution slots.
- `label`: the displayed name.
- `layout`: `call` (inline when it fits) or `block` (always indented).
- `slots`: a permutation containing every slot number exactly once.
- Optional `template`: plain text with numbered placeholders, e.g. `{0}={1}`
  or `IF {0} THEN {1}`. Numbers address children after the `slots` permutation.
  Every slot must appear exactly once. Escape literal braces as `{{` and `}}`.
  Newlines are supported; indentation uses multiples of four spaces relative
  to the containing document. Place a multiline child on its own template line
  to retain that indentation. Nested custom expressions are parenthesized to
  preserve grouping. `layout: block` forces multiline layout.
- Optional `when: proposition`: activates the template only for an arrow
  established to have sort `Prop`; otherwise the rule uses its ordinary label
  and layout. The seeded arrow rules use this guard.
- Optional `scope` and `entry` selectors for notation matching. `null` selects
  the absence of scope/entry information; omitting a selector matches any value.
- Optional `identity` matches Rocq's exact resolved notation identity, separating
  identical grammar keys and scopes declared in different modules. Seeded rules
  use it when that information is available.

```json
{
  "version": 1,
  "rules": [
    {
      "kind": "application",
      "key": "cjr.primitive_laws.raw_mapsto",
      "arity": 2,
      "label": "owns_raw",
      "layout": "call",
      "slots": [0, 1]
    }
  ]
}
```

For example, an equality rule can add `"template": "{0}={1}"`. A CJR
conditional uses `"template": "if ({0}) {{\n    {1}\n}} else {{\n    {2}\n}}"`.
The JSON string encodes newlines as `\n`; the renderer expands them into lines.
Rules without `template` retain their existing call/block rendering.

Templates are plain text and numbered children, not executable code or raw HTML.
The renderer preserves each child document's symbols, binders, links, and nested
scope. Duplicate selectors, ambiguous equally specific matches, missing slots,
extra slots, unknown fields, and malformed files are rejected.

With `--learn`, choose a numbered encountered construct to teach or replace.
The CLI shows the source and every numbered slot, accepts JSON containing
`label`, `layout`, `slots`, and optional `template` and `when`, then writes a
local HTML preview. Guarded templates preview their propositional form; actual
rendering still requires semantic classification. A rule is saved
only after answering `y` to its acceptance prompt. Blank input skips a template;
`done` exits learning. `remove NUMBER` previews a deletion for confirmation.
EOF or interruption cancels learning without saving an unaccepted rule.
For single-page rendering, previews live in a dedicated `.preview` directory.

Scope and binder slots remain present, but user-authored labels and permutations
require human review: preserving the tree's content does not prove that arbitrary
wording conveys its meaning correctly.

## Errors, limits, and verification

File-level parser/context errors are displayed in the generated page and report;
other files still generate. Any failed file returns exit status 1. `--strict`
also returns 1 for unmapped notation or unsupported declarations/terms. Missing
dependencies, backend errors, and timeouts are reported rather than guessed.
No proof admissions are introduced; coq-lsp's failed-Qed admission recovery is
explicitly disabled.

`--timeout SECONDS` bounds each backend request (default 600 seconds). Large
developments may need a larger value because the backend checks earlier proofs
and maintains their document states. Partial HTML is not presented as complete
coverage; consult `report.json` before using it for review.

Tests use actual Rocq ASTs and check project boundaries, digest validation,
scope layout, rule learning/reloading, HTML escaping, local shadowing, cross-file
and constructor/field links, proof omission, deterministic generation, and
representative CJR contracts. The renderer is optional and does not change the
existing proof verification targets.

To render a selected source set while retaining project load paths, use `build --sources FILE_OR_DIRECTORY ... --output OUTPUT`. Example Makefiles use this to render compiled declarations while keeping scratch proof fragments as source assets. Repository examples now live under `example/<name>/`; each owns its rendered output in `docs/rocq/`.
