# szemeredi submission source

Minimal submission snapshot for the LeanEval problem `szemeredi` (statement revision 1), benchmark commit
`0e093293afbe96be91504ae6e44947876d3fc84e` (Lean `v4.35.0-rc3`, Mathlib
`5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`). `lakefile.toml` and `lean-toolchain` are copied byte-for-byte
from the generated official workspace; only `Submission.lean` and `Submission/**` are new.

## Attribution

Szemerédi's theorem is obtained from the density Hales–Jewett development of Gabriel Dahia
(<https://github.com/gdahia/densityhalesjewett>), as packaged in Lean Pool `LeanPool/DensityHalesJewett`
at lean-pool `5e0b39aee56fe9e23bae9bed852a42fef9260b92` (Apache-2.0). That project is newer than the
benchmark-pinned lean-pool, so its 14 files are **vendored** under `Submission/DHJ/` (module renames and a
provenance line only; see `NOTICE.md`). This submission adds only the bridge from the finite statement
`Combinatorics.ArithmeticProgression.exists_of_density_nat_atTop` to the benchmark's positive-upper-density
formulation.

Local checks (macOS, pinned dependencies): all Submission files, the trusted `Solution`, and `Challenge`
compile; `#print axioms Submission.szemeredi` is `[propext, Classical.choice, Quot.sound]`. Official
comparator and nanoda acceptance are not presumed.

Campaign: `trureturing` (Claude orchestration, Codex CLI implementation, independent Codex CLI and Claude
review).
