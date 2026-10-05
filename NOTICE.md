# Source attribution

This is a compatibility port of the full Klartag packing proof from
`mlgraham/lean-eval-klartag-submission`, immutable commit
`270b3358a135f64a6688636660c07772e8db0173`:
<https://github.com/mlgraham/lean-eval-klartag-submission/tree/270b3358a135f64a6688636660c07772e8db0173>.
The original source is licensed under Apache License 2.0; its license is retained in `LICENSE`.
The original proof was produced with Claude Code under human guidance, according to
its [original submission metadata](https://github.com/leanprover/lean-eval-submissions/issues/1720). Its mathematics formalizes B. Klartag's lattice-packing construction.

The trureturing campaign reuses that proof and adapts it to the official LeanEval environment:
Lean 4.35.0-rc3, Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`, and
lean-pool `e9d53e9cbcff8dfd0cc816ba94db7a26b082929f`.
Codex CLI performs the compatibility changes and verification. The substantive
proof and mathematical construction are attributed to the original source; this port
makes no claim to have originated them.

Changes address current Gaussian law/measurability interfaces, algebraic structure
transparency and matrix equivalences, probability pushforward instances, and actual
compiler/linter compatibility. All final quantifiers, hypotheses and conclusions
of the benchmark's `klartag_packing` statement are preserved.
