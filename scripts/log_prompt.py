#!/usr/bin/env python3
"""Append a user prompt from stdin with its UTC recording time."""

import argparse
from datetime import datetime, timezone
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--file", type=Path,
        default=Path(__file__).resolve().parent.parent / "logs" / "prompts.txt",
        help="prompt log destination (default: logs/prompts.txt)",
    )
    args = parser.parse_args()
    prompt = sys.stdin.read()
    if not prompt.strip():
        parser.error("the prompt on stdin must not be empty")
    timestamp = datetime.now(timezone.utc).isoformat(timespec="seconds")
    args.file.parent.mkdir(parents=True, exist_ok=True)
    with args.file.open("a", encoding="utf-8") as log:
        log.write(f"[{timestamp}]\n")
        log.write(prompt)
        if not prompt.endswith("\n"):
            log.write("\n")
        log.write("\n")


if __name__ == "__main__":
    main()
