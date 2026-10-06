# Unbounded derived solidification constructor

This source-only project constructs the left derived solidification functor
on **all integer-indexed unbounded complexes**, its adjunction to the literal
protected derived inclusion, the ordinary-unit-induced counit and the total
left-derived/right-Kan universal property for **all quasi-isomorphisms**.
The default positive root is `CWSolid.OriginalDerived`; it assumes neither
derived existence nor an adapted resolution. D(Solid) realization uses the
proved generator comparison, augmented free resolution and two truncation
telescopes.

Requires Elan, Git and network access for the pinned Mathlib dependencies.
From this directory:

```sh
ulimit -n 65536
lake exe cache get
lake build +CWSolid.OriginalDerived
# Equivalent positive default:
lake build
```

The positive root prints its standard axiom closures. The complete custom
source closure is included; no local absolute path or shipped cache is needed.
Saved successful official-pin logs and receipts are in `evidence/`.

The **explicitly partial** original benchmark is a separate opt-in target:

```sh
lake build +ChallengeIntegrated +IntegratedTargetAudit
lake env lean -j 1 -DElab.async=false -DautoImplicit=false src/IntegratedTargetAudit.lean
```

The audit prints all twelve literal target types: holes **1–9** have only
`propext`, `Classical.choice`, `Quot.sound`; **10–12** expose `sorryAx`.
Hole10 remains visibly unproved; holes11–12 depend on it. This package makes
**no complete official solve claim** and contains no negative certificate.
Protected signatures and non-hole definitions are unchanged.

Pins: Lean `4.35.0-rc3`, Mathlib
`5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`, `autoImplicit=false`.
Attribution and licenses: `NOTICE.md`, `LICENSE`, `provenance.json`.
`SHA256SUMS` and `sha-manifest.json` use relative paths.
