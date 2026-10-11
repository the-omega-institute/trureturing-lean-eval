# FLT source checkpoint — 2026-10-11

This checkpoint saves eleven verified repairs in the ongoing port of
`anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source files are complete canonical modules; patches show this checkpoint's changes
against the immediately preceding local port. Import adaptation for the official
submission is performed separately in the active FLT workspace.

CuspForm uses an explicit residue-field cancellation proof. Deformation uses the
current polynomial coefficient API and limits legacy implicit-argument transparency
to `namespace Univ`. Both retain their original hypotheses and conclusions.

The eleven repaired modules passed the canonical single-job `make lean` entry
with `--trust=0` and kernel type checking enabled. CuspForm and Deformation
also have successful associated theorem checks. The latest HeckeEis repair
uses an explicit `zsmul_eq_mul` application for the ZMod target; its associated
theorem check has also passed make/kernel validation. The attached receipts record the repaired source modules. The final versions
of all eleven repaired source modules have now passed checks without warnings;
unchanged supplier modules retain some existing warnings.

This is a progress checkpoint. The complete Submission root, comparator,
full-root Nanoda check, and official acceptance are pending. No new solve credit
is claimed. `LICENSE`, `NOTICE`, and `ATTRIBUTION.md` preserve supplier attribution.

Specialization-map surjectivity removes unavailable optional simp-attribute names
from one previously unverified module. The original theorem and proof body are
unchanged. A prior successful Lean environment query identified the names, and
the repaired complete module passed a fresh make/kernel check. Its patch starts
after the three earlier individual attribute removals by the existing watcher.

The associated specialization-surjectivity theorem card also passed the same
canonical single-job make/kernel validation (kernel 6.92 seconds),
with empty stdout and stderr. The same missing optional attributes were removed
after actual Lean failures; the patch starts after the existing watcher removed
the first four names. A prior successful environment query confirms the remaining
four absent names. Its theorem statement and proof body are unchanged. The new
receipts are saved under `receipts/PlaceSpecialization-theorem-card/`.

The projective-model multiplication proof uses the current extended-natural
cardinality formula for multivariate-polynomial Krull dimension, with explicit
`ENat.card_eq_coe_fintype_card` and `ENat.WithBot.coe_eq_natCast` applications.
Three proof-valued `haveI` bindings were changed to `have` to clear the actual
style warnings. The complete repaired module passed make/kernel validation
(kernel 14.16 seconds) with empty stdout/stderr. Its theorem statements are
unchanged; both actual failed diagnostics are retained. Its associated theorem
card also passed make/kernel validation (kernel 39.20 seconds) with
empty stdout/stderr.

The Herbrand norm-product theorem card removes four unavailable instance names
only after source-bound Lean failures rejected each one. A targeted query in
that exact theorem environment resolved all 57 remaining optional attribute
names. The diagnostic command was then removed, and the final complete theorem
passed the canonical single-job make/kernel check (kernel 6.17 seconds), with
empty stdout and stderr. Its statement and proof body are unchanged. The patch,
all four failed diagnostics, the successful query, and the final successful
receipts are saved under `receipts/Herbrand-norm-theorem-attributes/`.

The Cerednik–Drinfeld ribbon module now obtains ambient finite generators using
`AddGroup.fg_iff'`, uses the current finite-group instance, and calls
`AddCommGroup.finite_of_fg_isAddTorsion`. The reported proof-binding style
warnings were corrected. Its complete module passed the canonical single-job
make/kernel check with no warnings and an axiom closure containing only
`propext`, `Classical.choice`, and `Quot.sound`. The solution statement is unchanged.

The DVR approximation module removes four optional instance attributes rejected
by the actual compiler, updates deprecated API calls, and clears the reported
style, unused-variable, and overlapping-instance warnings. The induction helper
now binds its ring and group parameters explicitly. The final full module passed
the canonical single-job make/kernel check with empty stdout and stderr
(kernel 18.56 seconds); its diagnostic query was removed and the solution
statement remains unchanged. Failed and successful receipts are retained.

The associated DVR approximation theorem card also passed complete make/kernel
validation with empty stdout and stderr. It removes the same four optional
instance names only after actual compiler failures. Its theorem statement and
proof body are unchanged; original source binding and all terminal receipts
are preserved under `receipts/DVR-approximation-theorem-card/`.

The modular-curve SW local-old auxiliary proof now supplies the exact bundled
`AddMonoidHom.map_zsmul` application for its `ZMod p` character, after the generic
rewrite failed to infer it. Reported binding-style warnings were corrected and
unused parameter names were prefixed with underscores. The original hypotheses
and conclusion remain intact. The complete module passed make/kernel validation
(kernel 9.65 seconds) with empty stdout and stderr.

The HeckeEis source was subsequently updated to the current coefficient-zero
and dependent-if lemmas, and its reported proof-binding style warnings were
cleared. The complete final module passed a fresh make/kernel check with empty
stdout and stderr. Its solution statement is unchanged; the original scalar
compatibility repair is retained alongside this warning-cleanup patch.

CuspForm replaces the retired strict-product bound with its constituent
`mul_le_of_le_one_left`/`trans_lt` proof, updates deprecated conditional,
valuation, hom-coercion and function-coercion names, and removes the actual
no-op tactic. Deformation uses the current conditional lemmas. Both complete
final modules passed fresh single-job make/kernel validation without warnings;
their solution statements and earlier substantive compatibility repairs remain
intact. Their original diagnostics and final receipts are retained.

The standard-smooth localization module now uses the official Mathlib's
one-based `List.TFAE.out` indices (`.out 5 1`). The reported deprecated tactic,
polynomial equivalence, and local declaration style were updated. All theorem
statements are unchanged. The complete repaired module passed canonical
single-job make and kernel checks (kernel 27.34 seconds), with empty stdout and
stderr. Original failure receipts and the exact patch are retained under
`receipts/StandardSmooth-localization-TFAE/`.

The associated standard-smooth localization theorem card also passed make and
kernel validation (kernel 43.41 seconds), with empty stdout and stderr. Its
source was unchanged. The complete source and terminal receipts are retained.

The modular-curve canonical-divisor degree theorem card now removes eight
optional simp references that are absent from its imported environment. Each
removed name has a source-bound Lean failure: three were rejected individually,
and a targeted diagnostic rejected the remaining five in one run. The temporary
diagnostic was removed. The original theorem statement and proof body are
unchanged, and the complete final module passed canonical single-job make and
kernel checks (kernel 29.61 seconds), with empty stdout and stderr. Original and
final source, the patch, and failed and successful receipts are retained under
`receipts/ModularCurve-canonical-divisor-theorem-card/`.
