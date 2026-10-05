# annals_fractional_expectation_thresholds submission source

Minimal submission snapshot for the LeanEval problem `annals_fractional_expectation_thresholds`
(statement revision 1), benchmark commit `0e093293afbe96be91504ae6e44947876d3fc84e` (Lean `v4.35.0-rc3`,
Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`, lean-pool `e9d53e9cbcff8dfd0cc816ba94db7a26b082929f`).
`lakefile.toml` and `lean-toolchain` are copied byte-for-byte from the generated official workspace; only
`Submission.lean` and `Submission/*.lean` are new (the official intake overlays them onto the canonical
workspace, which supplies `ChallengeDeps`).

## Attribution

The mathematics is the Frankston–Kahn–Narayanan–Park theorem (Annals of Math. 194 (2), 2021), obtained here
from the stronger Park–Pham (Kahn–Kalai) theorem, which is **reused** from
[Lean Pool](https://github.com/Vilin97/lean-pool) `LeanPool/KahnKalai` (`KahnKalai.park_pham_bound`;
Apache-2.0; by Dan Clemens Posch, upstream <https://github.com/dcposch/kahn-kalai-lean>, following
arXiv:2303.02144), imported as the benchmark allows for solutions. This submission adds the transport to the
benchmark's formulation: universe change to `Fin n`, minimal elements and the bound by `l`, the identity
between Mathlib's `setBernoulli` measure and the pool's explicit measure, monotonicity of the Bernoulli
measure of an upper family in `p`, comparison of the challenge's `p_c` with the pool threshold, integral
covers as fractional covers, and the change from `log₂` to `ln` (`K = 100000 / log 2`).

Local checks (macOS, pinned dependencies): `Submission`, the trusted `Solution`, and `Challenge` compile;
`#print axioms` for `theorem_1_1` and `K` is `[propext, Classical.choice, Quot.sound]`. Official comparator
and nanoda acceptance are not presumed.

Campaign: `trureturing` (Claude orchestration, Codex CLI implementation, independent Codex CLI and Claude
review).
