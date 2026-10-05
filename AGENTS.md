# Agent Notes

- Do not leave linter warnings behind in edited files.
- Treat linter warnings as follow-up work to fix before considering a task complete.
- When adding new Lean files or changing existing ones, run an appropriate build/check and clean up warning output, not just errors.

## Fixed submission identity

- Canonical main repository: `the-omega-institute/trureturing`. Competition source repository: `the-omega-institute/trureturing-lean-eval`. Official issue destination: `leanprover/lean-eval-submissions`.
- The exact official `Model` is `trureturing`. Verify it with `gh repo view the-omega-institute/trureturing --json name`; reject any different Model, including `trureturning`. Preserve source, production description, and publication metadata.
- `scripts/check_submission_identity.py` is read-only: require `--check` or `--dry-run`, `--title`, and `--body-file`. Supply `--official-parser-dir` containing unchanged official `fetch_submission.py` and `validate_submission_intake.py` for full intake validation. A successful dry-run is not proof or benchmark acceptance.
- Check campaign issue #1 and owned official issues (including closed) to avoid unintended duplicate submissions. A new statement revision or an explicitly authorized metadata correction may be resubmitted; link the original issue and explain the supersession.
