# Notices for the Zhang bounded prime gaps submission

The upstream projects listed below are licensed under Apache License 2.0. Their original copyright and author notices remain in the vendored Lean files. The packaging orchestrator supplies the Apache LICENSE and this NOTICE.md at the generated workspace root.

## AxiomMath/PrimeGapsLib

- Repository: https://github.com/AxiomMath/PrimeGapsLib
- Commit: `1faa7b14e82ddebc2772dfb9153922f01b106477` (source pin `1faa7b14`).
- License: Apache-2.0, verified from the upstream LICENSE (SHA-256 `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`).
- Copyright notices retained in source include: Copyright (c) 2026 Axiom Math. All rights reserved..

No upstream NOTICE file is present in the available pinned source tree.

## kimihiro64/bombieri-vinogradov

- Repository: https://github.com/kimihiro64/bombieri-vinogradov
- Commit: `7a1748306e026825ed6a5555516cc2f28989b2ac` (source pin `7a174830`).
- License: Apache-2.0, verified from the upstream LICENSE (SHA-256 `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`).
- Copyright notices retained in source include: see individual source headers.

No upstream NOTICE file is present in the available pinned source tree.

## AlexKontorovich/PrimeNumberTheoremAnd

- Repository: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
- Commit: `0f15a38c` (source pin `0f15a38c`).
- License: Apache-2.0, verified from the upstream LICENSE (SHA-256 `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`).
- Copyright notices retained in source include: Copyright (c) 2022 Abby J. Goldberg. All rights reserved.; Copyright (c) 2023 Arend Mellendijk. All rights reserved.; Copyright (c) 2024 Arend Mellendijk. All rights reserved.; Copyright (c) 2024 James Sundstrom. All rights reserved.; Copyright (c) 2024 Lawrence Wu. All rights reserved.; Copyright (c) 2024 Michael Stoll. All rights reserved.; Copyright (c) 2025 Maksym Radziwill. All rights reserved.; Copyright (c) 2025 Stefan Kebekus. All rights reserved.; Copyright (c) 2026 Matteo Cipollina. All rights reserved.; Copyright (c) 2026 Robby Sneiderman. All rights reserved.; Copyright (c) 2026. All rights reserved..

No upstream NOTICE file is present in the available pinned source tree.

## kimihiro64/Robin1984

- Repository: https://github.com/kimihiro64/Robin1984
- Commit: `bfa72aec` (source pin `bfa72aec`).
- License: Apache-2.0, verified from the upstream LICENSE (SHA-256 `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`).
- Copyright notices retained in source include: see individual source headers.

No upstream NOTICE file is present in the available pinned source tree.

## Provenance and modifications

PrimeNumberTheoremAnd was obtained from the AlexKontorovich repository archive at 0f15a38c. The previous port manifest identifies the same revision through the kimihiro64/PrimeNumberTheoremAnd fork; retained per-file provenance follows that manifest.

Vendored imports were relocated into Submission.PGL, Submission.KBV, Submission.PNT and Submission.Robin. Blueprint/Architect metadata was removed, and Lean/Mathlib API names, proof elaboration and linter style were migrated. KBV residue-count and Bombieri–Vinogradov proposition names were renamed to avoid collisions; the final bridge is checked by definitional equality. Documentation-only example axioms were removed. Mathematical statements and certificate-checking logic are preserved. The detailed prior port modification summary follows below.

The k50e25d25n1295.json certificate from AxiomMath/PrimeGapsLib is now embedded byte-for-byte in CertificateText.lean (SHA-256 `99808e1d95204c5bbc0cde845641cfdbb41ea950fa7fa9858df8bd093111787a`). SourceGen.readRaw parses this public exposed string instead of reading a sidecar file. Generated data remains untrusted and checked by the original kernel proofs. All vendored Lean files carry the required modification comment. JSON, provenance sidecar and per-repository LICENSE files were removed from Submission/ so the Lean-only overlay is self-contained.

# Port edits

- Rename deprecated Lean `Bool.and'`, `Bool.or'`, `Bool.not'` to `Bool.and`, `Bool.or`, `Bool.not` in certificate kernels and soundness proofs. Remove now-reflexive primed/unprimed equality lemmas from simp lists. No mathematical statement changed. Files:
  - PGL/PrimeGapsCert/Gap246/Moments/LadderSound.lean
  - PGL/PrimeGapsCert/Gap246/Moments/TableSound.lean
  - PGL/PrimeGapsCert/Gap246/Moments/CheckSound.lean
  - PGL/PrimeGapsCert/Gap246/Moments/BoundSound.lean
  - PGL/PrimeGapsCert/Gap246/Sparse/RhsIndexSound.lean
  - PGL/PrimeGapsCert/Gap246/Sparse/WeightBase.lean
  - PGL/PrimeGapsCert/Gap246/Sparse/WeightSound.lean
  - PGL/PrimeGapsCert/Gap246/Sparse/WeightCore.lean
  - PGL/PrimeGapsCert/Gap246/Sparse/RhsFeatureSound.lean
  - PGL/PrimeGapsCert/Gap246/Sparse/LhsSound.lean
  - PGL/PrimeGapsCert/Gap246/Kernel/MomentBound.lean
  - PGL/PrimeGapsCert/Gap246/Kernel/LHSScalar.lean
  - PGL/PrimeGapsCert/Gap246/Kernel/LHS.lean
  - PGL/PrimeGapsCert/Gap246/Kernel/RHS.lean
  - PGL/PrimeGapsCert/Gap246/Kernel/Folds.lean
  - PGL/PrimeGapsCert/Gap246/Kernel/Moments.lean
  - PGL/PrimeGapsCert/Gap246/Moments/Direct/DataCheckSound.lean

- Rename KBV `Real.primeCountingZMod` to `Real.kbvPrimeCountingZMod`, and its root proposition to `KBVBombieriVinogradov`, to avoid duplicate declarations with PGL. All KBV references are updated. Their definitions remain identical to PGL; final bridge uses definitional equality and reorders conjuncts, deriving `q - p ≤ 246` by `omega`.
- Use KBV Solution.lean, which has the actual proved theorem; do not vendor its sorried Challenge.lean.

- Include the 54 KB certificate JSON consumed by source generators (byte-identical copy plus provenance sidecar). Generated data is still verified with the upstream kernel proofs. Serial cache invalidation tracks this asset for generator consumers.

- Migrate deprecated Lean conditional lemmas using the compiler-recommended names: {'if_pos': 'ite_eq_left', 'if_neg': 'ite_eq_right', 'if_true': 'ite_true', 'if_false': 'ite_false', 'dif_pos': 'dite_eq_left', 'dif_neg': 'dite_eq_right'}. Applied in 154 files, listed in `zhang_ite_rename_files.json`. Proof and statement structures unchanged.

- `PGL/PrimeGapsCert/Gap246/Sparse/SignedSound.lean`: remove two trailing `all_goals norm_num` commands; the preceding tactic now closes every goal and the unused-tactic linter rejects the redundant commands.

- `PGL/PrimeGapsTheory/Analysis/Tonelli/LpGeneral.lean`: current Mathlib MemLp is norm finiteness, with measurability encoded in eLpNorm. Replace pair projections by `aestronglyMeasurable` and `eLpNorm_lt_top`, supply measurability to seminorm formulas, and adapt MemLp constructors to the current finiteness definition. Existing Mathlib definitions/lemmas searched in LpSeminorm/Defs.lean and Basic.lean. Statements unchanged.
- The same module's `Lp.integralLeftₗ` now needs a local `maxHeartbeats 800000` elaboration budget (default 200000 timed out). This changes elaborator limits only; memory watchdog remains active.

- `PGL/PrimeGapsTheory/Variational/SmoothApprox.lean`: provide `hmeas` to `eLpNorm_eq_lintegral_rpow_enorm_toReal`; update `eLpNorm_add_le` to its current single exponent-bound argument. Current signatures searched in Mathlib LpSeminorm/Defs.lean and TriangleInequality.lean. Statements unchanged.

- Migrate proposition-valued local instances (`haveI`/`letI` of IsFiniteMeasure, Nonempty, NeZero, Finite, Fact, Countable, SFinite, IsProbabilityMeasure) to `have`, as required by current `linter.style.haveILetI`. Data-valued instances are retained. Files listed in `zhang_instance_style_files.json`.

- `PNT/PrimeNumberTheoremAnd/Fourier.lean`: remove redundant `Circle.norm_coe` from a `simp` call; current Mathlib's default simp set already handles the norm and flags this argument as unused.

- Rename the old two-hypothesis `Finset.prod_le_prod` (nonnegativity plus pointwise bound) to current `Finset.prod_le_prod₀`, found in Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean. The new unadorned lemma only applies in ordered monoids with globally monotone multiplication, hence the failed MulLeftMono ℝ synthesis. Files listed in `zhang_product_rename_files.json`. Statements unchanged.
- `PGL/PrimeGapsTheory/Arithmetic/TdDecomposition/SizeHyp.lean`: rename deprecated one-hypothesis `Finset.prod_le_prod'` to current `Finset.prod_le_prod` (natural-number product bound).

- `PGL/PrimeGapsTheory/Analysis/SpecificSums.lean`: update convert subgoal handling in the telescoping sum proof. Normalize natural casts and prove denominator equality by ring; normalize the two initial zero summands by norm_num. The old rfl/grind/simp three-goal sequence no longer matches elaboration. Statements unchanged.

- Likewise migrate old nonnegative-product lemmas `prod_le_prod_of_subset_of_one_le` and `prod_le_one` to their `₀` variants. Current signatures searched in Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean. Files listed in `zhang_more_product_rename_files.json`.

- `PGL/PrimeGapsTheory/Arithmetic/Mertens/CoprimeDensity/PartialBounds.lean`: replace deprecated Nat.sq_mul_squarefree with exists_sq_mul_squarefree. The current theorem binds square-factor then squarefree-factor, so swap which choose projection defines fb/fa, preserving their roles and the existing equation. Current theorem found in Mathlib/Algebra/Squarefree/Basic.lean. Statements unchanged.

- `PGL/.../Arithmetic/HAsymptotic/ConvForm.lean` and `PGL/.../Sieve/S2m/QFactor.lean`: replace removed Batteries.Data.Nat.Gcd import with cached Mathlib.Data.Nat.GCD.Basic. The latter imports the current core gcd API. Import manifest updated. No dependencies were built or downloaded.

- `PNT/PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Growth.lean`: replace removed Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic import with Integrability.Log, where current MeromorphicOn.circleIntegrable_log_norm is declared. Cached olean exists; no Mathlib compile. Full external-import cache preflight found no other unavailable modules after these path renames.

- Extend instance-style migration to data-valued instances inside proposition proofs: current linter tests the goal being Prop, not the instance type. Replace remaining `haveI` with `have`, and proof-local `letI` with `let`. Retain `letI` in the two data definitions unitCharacterSum and fareyIndices (their values depend on finite enumerations). Linter source inspected at Mathlib/Tactic/Linter/HaveILetI.lean. Files listed in `zhang_proof_instance_style_files.json`. Statements unchanged.

- Rename deprecated Finset.single_le_prod' to Finset.single_le_prod. Current alias and signature found in Mathlib/Algebra/Order/BigOperators/Group/Finset.lean. Files listed in `zhang_single_product_rename_files.json`. Statements unchanged.

- Rename deprecated Finset.one_le_prod' to Finset.one_le_prod, as confirmed by the alias in Mathlib/Algebra/Order/BigOperators/Group/Finset.lean. Files listed in `zhang_one_product_rename_files.json`.

- Convert standalone Architect `blueprint_comment /-- ... -/` commands to ordinary `/- ... -/` comments. The initial attribute/import stripper missed these commands; their absence of a parser caused cascading errors and synthetic-sorry diagnostics in MellinCalculus (no source sorry was added). This removes only nonsemantic blueprint commands, retaining their prose. File/count list: `zhang_blueprint_comment_files.json`.

- `PNT/PrimeNumberTheoremAnd/MellinCalculus.lean`: after current elaboration unfolds Set.prod to a membership predicate, restore the definitionally equal `volume.restrict (Tx ×ˢ Ty)` presentation with `change` before the existing product-measure rewrite. This is only definitional normalization; no theorem statement or mathematical argument changed.

- `PNT/PrimeNumberTheoremAnd/MediumPNT.lean`: inline the two constituent inequalities from the deprecated mul_lt_one_of_nonneg_of_lt_one_left proof: `(mul_le_of_le_one_right ...).trans_lt ...`. Mathlib explicitly gives no replacement name; its existing proof was inspected in Algebra/Order/GroupWithZero/Basic.lean. No new lemma or statement change.

- `PNT/PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/CanonicalProduct.lean`: present the Weierstrass factor as pointwise multiplication of two explicit functions via `change` before using current logDeriv_mul. The existing lambda is definitionally equal but no longer matched by rewrite's function metavariable inference. Current signature inspected in Mathlib/Analysis/Calculus/LogDeriv.lean. Statement unchanged.

- `KBV/BombieriVinogradov/Helpers/DirichletCharacter/AbelKernelDerivative.lean`: replace the unnecessary focused `<;>` by ordinary `;` in `convert hProduct using 1; try rfl`, following linter.unnecessarySeqFocus. The current conversion produces one remaining goal. Statement unchanged.

- `PNT/PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/CartanBound.lean`: current Real.posLog_le_posLog takes `-1 ≤ x` rather than `0 ≤ x`; supply `neg_one_lt_zero.le.trans (by positivity)` at two calls. Current signature/examples inspected in Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean. Statements unchanged.

- Correct the instance-style migration in `PNT/.../Complex/CartanMajorantBound.lean`: retain its three TERM-level `letI` binders in theorem statements. The linter applies only to proof tactics; changing term-level letI introduced an extra let binder and shifted intro names. The original statement binders are restored exactly. All other migrated local instance occurrences were inspected as proof tactics, except the two previously preserved data definitions.

- Deprecated Mathlib Real/Complex Basic, Complex BigOperators, and Set Lattice imports replaced with the current shim public imports in 300 files (list: zhang_deprecated_import_files.json). No proof statements changed.
- LogQuadraticAbsorption: use Nat.add_le_add_right directly; current norm_num simplified its inequality hypothesis away.

- CompletedProductLogDerivative: express pointwise multiplication as the function product in a calc intermediate, matching the current Mathlib logDeriv_mul rewrite shape; theorem unchanged.

- LevelCorrectionEulerProduct: normalize the function-valued finite product with current Finset.prod_fn when applying logDeriv_prod; theorem unchanged.

- StrongPNT: normalize the two finite function products with Finset.prod_fn between logDeriv_prod and logDeriv_mul/div rewrites, adapting the current Mathlib function-product API.

- PrincipalLevelCorrectionLogDerivativeBound: same Finset.prod_fn normalization as LevelCorrectionEulerProduct for current logDeriv_prod.

- ZetaFiniteOrder: simplify an intermediate complex pi-norm calculation with simp; current simp already proves the result and the old auxiliary norm steps triggered unnecessarySimpa warnings.

- HadamardLogDerivative: Finset.prod_fn converts the finite Hadamard product before logDeriv_prod; change exposes the pointwise four-factor product before logDeriv_mul. The two theorem statements are unchanged.

- LValuePositivity: replace unnecessary tactic <;> by ; as required by the current linter.

- ZetaSign: replace unnecessary tactic <;> by ; as required by the current linter.

- Serial driver expected-warning parser accepts Lean 4.35's backtick-delimited `declaration uses `sorry`` text for Challenge only. Submission and all vendored modules reject every warning.

