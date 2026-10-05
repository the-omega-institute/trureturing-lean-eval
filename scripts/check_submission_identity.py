#!/usr/bin/env python3
"""Check submission identity without creating or editing any issue."""

from __future__ import annotations

import argparse
import hashlib
import importlib
import json
import pathlib
import subprocess
import sys

MAIN_REPO = "the-omega-institute/trureturing"
MODEL = "trureturing"
DESTINATION = "leanprover/lean-eval-submissions"


def identity_section(body: str) -> str:
    """Read only the unique Model field when no official parser is supplied."""
    lines = body.splitlines()
    headings = [i for i, line in enumerate(lines) if line.split() == ["###", "Model"]]
    if len(headings) != 1:
        raise ValueError("body must contain exactly one ### Model section")
    start = headings[0] + 1
    end = next(
        (i for i in range(start, len(lines)) if lines[i].split()[:1] == ["###"]),
        len(lines),
    )
    return "\n".join(lines[start:end]).strip()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--check", action="store_true")
    modes.add_argument("--dry-run", action="store_true")
    parser.add_argument("--body-file", required=True, type=pathlib.Path)
    parser.add_argument("--title", required=True)
    parser.add_argument("--official-parser-dir", type=pathlib.Path)
    args = parser.parse_args()
    try:
        if not args.title.strip():
            raise ValueError("title must be non-empty")
        lookup = subprocess.run(
            ["gh", "repo", "view", MAIN_REPO, "--json", "name"],
            check=True, capture_output=True, text=True, timeout=20,
        )
        canonical = json.loads(lookup.stdout)["name"]
        if canonical != MODEL:
            raise ValueError(f"canonical lookup returned {canonical!r}; expected {MODEL!r}")
        print(f"Canonical lookup: {MAIN_REPO} -> {canonical}", flush=True)
        body_bytes = args.body_file.read_bytes()
        body = body_bytes.decode("utf-8")
        declared = identity_section(body)
        if args.official_parser_dir is not None:
            root = args.official_parser_dir.resolve(strict=True)
            for name in ("fetch_submission.py", "validate_submission_intake.py"):
                if not (root / name).is_file():
                    raise ValueError(f"official parser file missing: {root / name}")
            sys.dont_write_bytecode = True
            sys.path.insert(0, str(root))
            fetch = importlib.import_module("fetch_submission")
            intake = importlib.import_module("validate_submission_intake")
            declared = fetch.find_issue_section(body, "Model")
        else:
            print("Official intake validation: NOT RUN (no --official-parser-dir)")
        if declared != canonical:
            raise ValueError(f"Model {declared!r} rejected; expected exactly {canonical!r}")
        if args.official_parser_dir is not None:
            fields = intake.validate_submission_issue(args.title, body)
            if fields["model"] != canonical:
                raise ValueError("official parser Model differs from canonical identity")
            print("Official intake validation: PASS")
            print(json.dumps(fields, ensure_ascii=False, sort_keys=True))
        print(f"Body SHA256 (read only): {hashlib.sha256(body_bytes).hexdigest()}")
        mode = "dry-run" if args.dry_run else "check"
        print(f"Identity {mode}: PASS; Model={canonical}; destination={DESTINATION}")
        print("Before manual submission: check source campaign issue #1 and owned official")
        print("issues (including closed); never repeat the same problem. #1968 replaces")
        print("closed #1967; unit #1969 already exists. No issue was created or edited.")
        print("This check does not establish proof or benchmark acceptance.")
        return 0
    except Exception as error:
        print(f"Submission identity check rejected: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
