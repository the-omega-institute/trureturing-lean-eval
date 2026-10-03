# Abelian power quotients: reusable Lean dependency

This branch publishes three unchanged, previously reviewed Lean source files
for the abelian precursor to Nikolov–Segal strong completeness. It is a
source-only publication, not a Lake package or an official LeanEval submission.
No package build was performed. The sources were checked separately against
the pinned public library through its canonical warm-cache build door.

For a compact Hausdorff commutative topological group `G`, a finite set `S`
whose generated subgroup is dense, and a positive integer `n`, the named theorem
`LeanEval.NikolovSegalDependency.compact_abelian_power_quotient` proves that
the subgroup `Gⁿ = range (g ↦ gⁿ)` is open and
`[G : Gⁿ] ≤ n ^ S.card`. Compactness closes the power-map image; the quotient
has exponent dividing `n`; the images of the dense generators give a surjection
from a product of `S.card` cyclic groups of order `n` onto that quotient.

`Checks.lean` checks `n = 1`, the empty generating set, equality of the index
bound for `(Z/nZ)^d`, and openness of every finite-index subgroup in the abelian
case. `SharpGeneratorCheck.lean` constructs a generating set of cardinality
`d` for those products when `n > 1`, and checks the specialization under
compactness and total disconnectedness, deriving Hausdorffness rather than
adding it as a premise.

The full theorem says that every topologically finitely generated profinite
group is strongly complete, including arbitrary nonabelian groups. The sources
here require commutativity. In a nonabelian group the power map need not be a
homomorphism, its image need not be a subgroup, and the cyclic-product argument
does not apply. These files do not provide the nonabelian verbal-subgroup
closedness and uniform word-width results needed for the full theorem.

Mathematical attribution: Nikolay Nikolov and Dan Segal, *On finitely generated
profinite groups, I: strong completeness and uniform bounds*, Annals of
Mathematics 165 (2007), 171–238, Theorem 1.1 (p. 172),
<https://doi.org/10.4007/annals.2007.165.171>.
The original paper is available at
<https://annals.math.princeton.edu/wp-content/uploads/annals-v165-n1-p05.pdf>.
This is literature-known dependency staging, with no mathematical novelty claim.

## Exact prerequisites and dependency

- Lean `leanprover/lean4:v4.33.0` (also recorded in `lean-toolchain`).
- Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Public trureturing commit `586ff54dc5fba0aaa4eab5b152048e0bc3daec23`:
  <https://github.com/the-omega-institute/trureturing/tree/586ff54dc5fba0aaa4eab5b152048e0bc3daec23>.
- Its existing `D5.S3.Factorization.Galois.GeneralPowerCharacterLayer` module:
  <https://github.com/the-omega-institute/trureturing/blob/586ff54dc5fba0aaa4eab5b152048e0bc3daec23/D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.lean>.
  The proofs directly reuse `powerSubgroup`,
  `power_quotient_has_exponent_dividing`, and
  `power_subgroup_le_iff_quotient_pow_eq_one`; they do not reprove that dependency.
- The library's canonical build prerequisites, including .NET 10, Git, make,
  and elan/Lean. Reuse an existing warm library checkout as donor.

## Reproduce the scoped checks

Check out this publication at its immutable commit, as linked by the Library
reference, and set the absolute paths below. `main_library` is the existing
trureturing `dev` checkout and remains the warm donor. Use your real host session
ID; do not invent one. The canonical command creates or reuses that session's
isolated worktree at the immutable dependency pin.

```sh
set -e
main_library=/absolute/path/to/trureturing
proof_checkout=/absolute/path/to/this/publication
session_id=${CODEX_THREAD_ID:-${CODEX_SESSION_ID:?real host session ID required}}
library_worktree="$(dirname "$main_library")/trureturing-$session_id"
make -C "$main_library" worktree KIND=math NAME=abelian-reproduction \
  DEST="$library_worktree" BASE=586ff54dc5fba0aaa4eab5b152048e0bc3daec23
test "$(git -C "$library_worktree" rev-parse HEAD)" = \
  586ff54dc5fba0aaa4eab5b152048e0bc3daec23
STRATALINT_LEAN_CACHE_DONOR_REPOSITORY="$main_library" \
  make -C "$library_worktree" lean \
  LEAN_TARGETS='D5.S3.Factorization.Galois.GeneralPowerCharacterLayer Mathlib.Topology.Algebra.Group.ClosedSubgroup Mathlib.Topology.Algebra.Group.Quotient Mathlib.Topology.Algebra.OpenSubgroup Mathlib.Data.ZMod.Basic Mathlib.Data.Fintype.Pi Mathlib.Algebra.BigOperators.Pi Mathlib.Topology.Connected.TotallyDisconnected'

export ABELIAN_SOURCE="$proof_checkout"
export ABELIAN_OUTPUT="$library_worktree/build/preflight/abelian-check"
mkdir -p "$ABELIAN_OUTPUT"
cd "$library_worktree"
for module in AbelianPowerQuotient Checks SharpGeneratorCheck; do
  ABELIAN_MODULE="$module" bash tools/scripts/worktree/lean-cache-run.sh \
    lake env bash -c \
    'export LEAN_PATH="$ABELIAN_OUTPUT:$ABELIAN_SOURCE:$LEAN_PATH"; exec lean -R "$ABELIAN_SOURCE" -o "$ABELIAN_OUTPUT/$ABELIAN_MODULE.olean" "$ABELIAN_SOURCE/$ABELIAN_MODULE.lean"'
done
```

Only the named dependency/import targets and these three files are checked;
there is no full-root build. Each source check must exit zero. The named
declarations' printed axiom closure is limited to the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`.
Generated oleans and process evidence stay outside this source repository.

## Source seals and attribution

The exact SHA-256 seals are:

| Source | SHA-256 |
| --- | --- |
| `AbelianPowerQuotient.lean` | `f7772458d257ff4115474a70efd042c3abbd8332b06b77ba7f9e6b3b5b30cf7b` |
| `Checks.lean` | `3975622f6cf6f2da2de4d36d00b43c9d5d7c84909a37b79f487b704fe2ae2783` |
| `SharpGeneratorCheck.lean` | `cf868c207f171c5ac1d5b837ec5246ae09fa7713d43bc9531bcdc02acb77c74e` |

The supplied proof implementation came from Codex CLI session
`01a1027b-217a-7ad2-abbf-f73985705553`; its independent approval is supplied by
the controller. This publication was prepared by the sole Codex CLI delivery
worker `01a102eb-e367-7893-8e3d-ed86c2e809b9`, preserving all source bytes.
Campaign attribution is `trureturning`; publication creates no acceptance or
ranking claim. The reusable dependency belongs to the public trureturing
library; Lean and Mathlib supply its imported foundations.

The existing legacy official issue 1932 consumes immutable commit
`92adfe225bb26dfed06f5ba77d9abbb7f680733f`
on the separate Gardam unit-submission publication. This branch contains only
the abelian dependency sources and does not change that submission. The new
mathematics remains outside trureturing `dev`: a Library citation note is a
reference, not a formal-code port, atom deposit, freeze, or new D5 admission.
The repository's Apache-2.0 license is included as `LICENSE`; the paper is
cited, not redistributed here.
