# zhang_bounded_prime_gaps submission source

Submission snapshot for the LeanEval problem `zhang_bounded_prime_gaps` (statement revision 1), benchmark commit
`0e093293afbe96be91504ae6e44947876d3fc84e` (Lean `v4.35.0-rc3`, Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`).
`lakefile.toml` and `lean-toolchain` are copied from the generated official workspace; only `Submission.lean` and
`Submission/**/*.lean` are new.

## Attribution

The mathematics is reused, not original. The bound 246 is `bombieriVinogradov_implies_prime_gap_le_246` from
AxiomMath/PrimeGapsLib (`1faa7b14`), made unconditional by the Bombieri–Vinogradov theorem of
kimihiro64/bombieri-vinogradov (`7a174830`), with their dependencies kimihiro64/PrimeNumberTheoremAnd (`0f15a38c`)
and kimihiro64/Robin1984 (`bfa72aec`); all Apache-2.0. These are vendored under `Submission/` with renamed modules,
Lean 4.35 / Mathlib API ports, a per-file provenance line and a modification notice. The PrimeGapsLib numerical
certificate is embedded byte-for-byte as a Lean string (`CertificateText.lean`) and is still checked by the kernel.
Full provenance and the list of modifications are in `NOTICE.md`; this submission adds only the vendoring, the ports
and the final bridge to the benchmark statement.

Local checks (macOS): in a clean copy of the generated workspace containing only the submitted `.lean` files, every
module, `Submission`, the trusted `Solution` and `Challenge` compile with `-DautoImplicit=false`, and
`#print axioms` for the hole is `[propext, Classical.choice, Quot.sound]`. Official comparator and nanoda acceptance
are not presumed.

Campaign: `trureturing` (Claude orchestration, Codex CLI implementation, independent Codex CLI and Claude review).
