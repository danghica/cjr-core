# Prompt logging

For every new human user prompt in this repository, append its exact text to
`logs/prompts.txt` before starting work. Use `python3 scripts/log_prompt.py`
with the prompt supplied on standard input; it adds the UTC recording time.
Use literal input (for example a quoted heredoc), so shell syntax in a prompt
is never evaluated. Log follow-up prompts too, but do not duplicate prompts
already recorded in the current session, or log tool output and system messages.
Do not invent timestamps or reconstruct historical prompts with current dates.

Keep the prompt log and `build/verify.log` with the changes when the user asks
to commit or push. `make verify` refreshes the verification log and preserves
the check's exit status. Commit and push through the normal Git workflow.
