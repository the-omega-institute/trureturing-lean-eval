# FLT source checkpoint — 2026-10-11

This checkpoint saves two verified repairs in the ongoing port of
`anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source files are complete canonical modules; patches show this checkpoint's changes
against the immediately preceding local port. Import adaptation for the official
submission is performed separately in the active FLT workspace.

CuspForm uses an explicit residue-field cancellation proof. Deformation uses the
current polynomial coefficient API and limits legacy implicit-argument transparency
to `namespace Univ`. Both retain their original hypotheses and conclusions.

Each repaired module and its associated theorem module passed the canonical
single-job `make lean` entry with `--trust=0` and kernel type checking enabled.
The attached receipts record the repaired source modules. Existing linter and
deprecation warnings remain follow-up work before final delivery.

This is a progress checkpoint. The complete Submission root, comparator,
full-root Nanoda check, and official acceptance are pending. No new solve credit
is claimed. `LICENSE`, `NOTICE`, and `ATTRIBUTION.md` preserve supplier attribution.
