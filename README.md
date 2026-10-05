# hopf_s6_complex_structure submission source

Minimal submission snapshot for the LeanEval problem `hopf_s6_complex_structure` (statement revision 1),
benchmark commit `0e093293afbe96be91504ae6e44947876d3fc84e` (Lean `v4.35.0-rc3`, Mathlib
`5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`, lean-pool `e9d53e9cbcff8dfd0cc816ba94db7a26b082929f`).
`lakefile.toml` and `lean-toolchain` are copied byte-for-byte from the generated official workspace; only
`Submission.lean` and `Submission/Helpers.lean` are new.

## What this proves and where the mathematics comes from

The two holes (a `ChartedSpace (Fin 3 → ℂ)` atlas on the unit sphere of `ℝ⁷` and its
`IsManifold 𝓘(ℂ, Fin 3 → ℂ) ω` proof) are filled by **reusing** the public theorem
`Mathoverflow1973.SixSphereComplexAtlas.exists_complex_analytic_atlas` from
[Lean Pool](https://github.com/Vilin97/lean-pool) (`LeanPool/HopfProblem`, Apache-2.0, authored by Boris
Alexeev; a formalization of the construction claimed by Alpöge, 2026). Lean Pool is the dependency the
benchmark explicitly allows solutions to import. This submission contributes only a model-space transport
from `EuclideanSpace ℂ (Fin 3)` to `Fin 3 → ℂ` along the ℂ-linear equivalence
`EuclideanSpace.equiv (Fin 3) ℂ`; the generic transport code in `Submission/Helpers.lean` is adapted from
Lean Pool `LeanPool/HopfProblem/Threefold/SpecialPeriods7.lean` (private there, hence copied). No new
mathematical claim is made by this submission beyond the transport.

Local checks (macOS, against the pinned dependencies): `Submission`, the trusted `Solution`, and
`Challenge` compile; `#print axioms` for both holes is `[propext, Classical.choice, Quot.sound]`.
Official comparator and nanoda acceptance are not presumed.

Campaign: `trureturing` (Claude orchestration, Codex CLI implementation).
