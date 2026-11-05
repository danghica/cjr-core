---
name: cjr-commit
description: Save prompts and project descriptions and plans under work/prompts, run all CJR repository and workspace tests, verify all Rocq proofs, and commit the saved project inputs, Rocq and Cangjie sources, documentation, and fresh validation evidence. Use when a contributor asks to validate and commit CJR work; do not use merely to define or edit this skill.
---

# Validate and commit CJR work

Run the checks, preserve their evidence, and make a normal Git commit containing
the requested project changes. Invoking this skill to commit work authorizes the
commit after successful validation; do not ask again merely because committing
is the final step. Defining or editing the skill does not authorize a commit.
Do not push unless the user separately requests it.

## Establish the commit scope

Locate the target Git repository and read its `AGENTS.md`, README, Makefiles,
test configurations, dependency pins, and any workspace verification/test
runners created by `cjr-build-core`. Inspect the branch, worktree, index, and
existing staged changes before modifying the index. Respect unrelated user work;
ask about genuinely ambiguous commit scope rather than silently including it
or discarding it. In a checkout containing several CJR repositories, operate in
the intended repository and do not commit all sibling repositories implicitly.

Follow prompt logging requirements before other work. In this repository,
`logs/prompts.txt` and `build/verify.log` must accompany the commit. Preserve exact
prompt text, including intentional whitespace; do not rewrite the prompt log to
satisfy a generic whitespace check.

Identify every test suite and proof source in the repository and application
workspace, including untracked sources intended for the commit. In particular,
the existing root build adapters do not automatically include `work/specs`,
`work/code/test`, or the CLI. Use the workspace runners and inventory, not just
the root Makefile, to establish complete coverage.

## Save prompts and projects in work/prompts

Before staging, create or reuse `work/prompts` and save all available prompts
and project descriptions, definitions, and plans for the projects being
committed. Preserve the original prompt text, appended algebraic properties,
revisions, and the accepted plan; do not rely on conversation context alone.
Use `prompt.md` and `plan.md` for an existing single-project workspace, preserving
its established filenames. For multiple projects, use distinct named
subdirectories under `work/prompts` so that one project's inputs cannot
overwrite another's. Retain earlier project records and revisions.

Include a current verbatim copy of `logs/prompts.txt` as
`work/prompts/prompts.txt`, while keeping the original repository log too.
Copy other supplied project-input files into the appropriate project directory
and record their origin. Do not invent unavailable historical prompts or
reconstruct their recording times. If required project inputs are missing,
identify what is missing before claiming they have all been saved.

Maintain `work/prompts/projects.md` as an index of the saved projects, linking
each to its prompt, properties, plan, and existing implementation and
documentation locations. This preserves project inputs under `work/prompts`;
generated sources and documentation retain their established workspace paths.
Include every saved prompt, project record, revision, plan, and index in the
commit, including newly created files. Verify that the files exist on disk and
are tracked in the staged snapshot rather than excluded by an ignore rule.

## Run all tests and verify all proofs

Use the pinned toolchains and installed project environment. Execute all
applicable repository and workspace test suites, without an example filter:

- Run `python3 -m unittest discover -s tests` for the shared Python tools and
  embedded browser-logic checks, plus any other test commands declared by the
  current repository.
- Run `make test` for all checked-in Cangjie example tests.
- Build the current workspace CLI and run all tests under `work/code/test`,
  including extracted-code tests, algebraic-property runtime checks, and CLI
  integration tests. Use the current project's runners; do not invent a
  successful result when a runner or required artifact is missing.
- Check the generated documentation's local links and renderer error reports,
  including the CLI reference and architecture diagram when present.

Run `make verify` to refresh `build/verify.log` and
`build/proof-verification.json`. Preserve its actual exit status. Verify that
the proof inventory includes every repository module, not only the entries
that happened to be compiled previously. Build any omitted modules explicitly.

For application sources in `work/specs`, run their local proof verification
separately: compile every module, kernel-check all of them with `coqchk`, and
run the assumption audit for public correctness and algebraic-property
theorems. Reject admissions, aborted proofs, and new axioms that bypass proof
obligations. Record the full module and theorem inventory and inspect transitive
assumptions. Root `make verify` passing alone does not verify the workspace.

Ensure the Cangjie being tested corresponds to the current proved CJR sources:
use the recorded extraction process, regenerate when needed, and rebuild and
retest changed generated code. Refresh affected documentation with rocq-readable
and the CLI documentation generator, checking their results. Do not hand-edit
generated implementation code to conceal an extraction mismatch.

If there is no application workspace, mark its checks as not applicable with
that reason. Missing tools or required artifacts in an existing workspace are
failures or blockers, not reasons to mark checks not applicable. Inspect test
skips: missing required dependencies must not turn into a passing report.
Do not replace failing checks with narrower commands, disable tests, weaken
contracts, or fabricate successful evidence. Fix clear in-scope failures and
rerun affected checks; if unresolved, retain the failure evidence and stop
before committing. Report the specific blocker.

## Preserve evidence for the exact sources

Keep fresh proof logs and machine-readable verification records in their
established locations. Store additional repository test logs under
`build/commit-evidence/`; keep workspace proof records in `work/specs` and
workspace test results in `work/code/test`.

Create `build/commit-validation.json` summarizing the validation, with:

- Actual UTC start and completion times, toolchain versions, and pinned
  dependency revisions.
- Commands and working directories, exit statuses, test counts and skips, and
  explicit coverage of repository and workspace checks.
- Proof modules and audited theorems, compilation and kernel-check outcomes,
  and assumption-audit results.
- SHA-256 fingerprints of the verified Rocq sources, tested Cangjie sources,
  CLI/bridge sources, test harnesses, and relevant build/configuration inputs.
- The saved prompt and project-input inventory under `work/prompts`, with
  fingerprints identifying the inputs included in this commit.
- Relative paths and hashes for the supporting test and proof logs and reports.
- An overall result that is successful only when every required check passed;
  explain any genuine not-applicable entries.

Use real run times and outputs. When capturing output through a pipeline,
preserve the checked command's exit status rather than the logging command's
status. Keep the raw results; a summary saying "passed" is not sufficient
evidence. Do not assert that tests verify the bridge formally or that native
extraction is covered by the core's Rocq proof.

## Stage and commit

Review the final diff and explicitly stage the intended Rocq (`.v`) and
Cangjie (`.cj`) files, supporting build/configuration and extraction files,
test and benchmark harnesses, and documentation (Markdown, generated HTML,
styles, diagrams, and existing project PDF outputs where relevant). Explicitly
stage all saved prompts and project records under `work/prompts`. Include the prompt
log, `build/verify.log`, proof records, fresh test results, and validation
manifest in the same commit as the sources they describe.

The repository ignores most `.log` files. Use `git check-ignore` to diagnose
an evidence path and, when needed, force-add only the specific required evidence
files. Do not force-add entire build or workspace directories. Leave disposable
proof objects, Python caches, test executables, local SDKs, and machine-specific
environment files out of the commit; follow existing repository policy for any
deliberately tracked distributable CLI executable.

Inspect the staged diff and file list, ensuring that the staged source and
configuration bytes match the validated fingerprints and that all linked
evidence is included. Confirm that the `work/prompts` inventory is complete in
the staged snapshot and its prompt-log copy matches `logs/prompts.txt`. If
staged inputs differ, rerun the checks affected by
those differences and refresh the evidence before committing. Do not reset or
overwrite unrelated staged changes to achieve this.

Create a normal Git commit with a message explaining the project change and
its validation. Do not amend an earlier commit, bypass hooks, change global Git
identity, or push as part of this skill. If a hook modifies verified inputs,
revalidate those inputs and update the evidence before retrying the commit.
If identity or signing prevents the commit, report the exact remaining step
and preserve the staged work.

Confirm the created commit contains the intended sources, documentation,
all saved prompts and project records under `work/prompts`, the original
prompt log, verification log, and supporting evidence. Report the commit hash,
the passed checks, evidence locations, and any remaining unrelated worktree
changes. Do not claim a commit succeeded unless Git confirms it.
