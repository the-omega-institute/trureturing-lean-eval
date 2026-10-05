# klartag_packing submission source

Single-workspace, source-only snapshot for LeanEval `klartag_packing`, statement revision 1,
with benchmark base `0e093293afbe96be91504ae6e44947876d3fc84e`.
`lakefile.toml` and `lean-toolchain` are copied byte for byte from the official workspace.
The submission consists of `Submission.lean` and its local `Submission/**/*.lean` modules.
LeanEval supplies the protected challenge, solution and judges from its official environment.

This proof is reused from `mlgraham/lean-eval-klartag-submission`
`270b3358a135f64a6688636660c07772e8db0173` (Apache-2.0), with current API compatibility
changes by the trureturing campaign. See `NOTICE.md` for attribution.

The exact final theorem asserts one positive constant c for every natural n,
and an ellipsoid in real dimension n+1 of volume c*n^2 whose only integer point is zero.

Official comparator/nanoda acceptance must be established by the official submission
result. Local Lean checks are not reported as official acceptance.
