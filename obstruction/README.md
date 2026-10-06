# Original CW comparison: joint incompatibility certificate

The Lean theorem `CWComparison.official_holes7_9_10_joint_target_empty` proves that no compatible choices satisfy the literal original derived adjunction, CW-functor specification and natural singular-chain comparison in holes 7, 9 and 10 of `derived_solidification_free_CW_homology`.

The proof uses the convergent sequence times indiscrete Bool, with the identity-minus-successor-plus-constant-at-infinity endomorphism. The genuine derived adjunction inverts its free-derived image; the exact discrete singular image is not invertible. Naturality gives the contradiction. `OFFICIAL_SCOPE_DEFECT.md` describes the witness and the exact scope.

This is a statement-defect certificate, not a positive benchmark solution. It proves neither general objectwise/homology impossibility nor that adding a T2 hypothesis suffices. `evidence/OriginalChallenge.lean` preserves the original statement and is never imported by the proof.

## Reproduce

With Elan installed, run from this directory:

```sh
lake update
lake exe cache get
lake build
```

The project pins Lean 4.35.0-rc3 and mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`, with `autoImplicit = false`. The default root prints the exact theorem type, its recursive axiom closure, and six protected-definition equality checks. The archived verification exited 0; its only axioms are `propext`, `Classical.choice` and `Quot.sound`. `source-manifest.json` binds the unchanged sources to saved compilation artifacts. Local absolute paths inside historical receipts identify the original run; rebuilding uses only this directory and its pinned mathlib dependency.

## Attribution

New supporting proofs are released under Apache-2.0. Copied sources retain their attribution notices. The original challenge and LeanCondensed inputs come from `dagurtomas/LeanCondensed@339ecc99fdc4bdb68ef248c16da0148dce61a639`, Apache-2.0; mathlib is Apache-2.0. This package asserts no originality for the published solid-geometry methods.

Official discussion: <https://github.com/leanprover/lean-eval/issues/657>.
