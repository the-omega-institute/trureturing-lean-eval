# Agent Notes

- Do not leave linter warnings behind in edited files.
- Treat linter warnings as follow-up work to fix before considering a task complete.
- When adding new Lean files or changing existing ones, run an appropriate build/check and clean up warning output, not just errors.

## Fixed submission identity

- Canonical main repository: `the-omega-institute/trureturing`. Competition source repository: `the-omega-institute/trureturing-lean-eval`. Official issue destination: `leanprover/lean-eval-submissions`.
- The exact official `Model` is `trureturing`. Verify it with `gh repo view the-omega-institute/trureturing --json name`; reject any different Model, including `trureturning`. Preserve source, production description, and publication metadata.
- `scripts/check_submission_identity.py` is read-only: require `--check` or `--dry-run`, `--title`, and `--body-file`. Supply `--official-parser-dir` containing unchanged official `fetch_submission.py` and `validate_submission_intake.py` for full intake validation. A successful dry-run is not proof or benchmark acceptance.
- Never repeat a submission for the same problem. Before any actual submission, check campaign issue #1 in the source repository and existing owned issues in the official destination, including closed issues. Highdim (`poincare_high_dim_topological`) #1968 replaces closed #1967; unit (`annals_unit_conjecture`) #1969 already exists.
- This identity-check task must never create or edit official issues. Commit, push, and PR operations belong to the controller.
