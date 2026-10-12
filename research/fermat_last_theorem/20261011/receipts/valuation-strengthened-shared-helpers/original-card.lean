import Submission.Supplier.Definitions.Def_FLTPrelim_Ramification
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ValuationSubring_exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open NumberField IsDedekindDomain

theorem ValuationSubring.exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation
    (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L']
    (p₀ : ℕ) (hp₀ : p₀.Prime) (x : (L' : Type)ˣ) (v : HeightOneSpectrum (𝓞 L'))
    (q : ℕ) (hq : q.Prime) (hqv : (q : 𝓞 L') ∈ v.asIdeal)
    (hv : ¬ ((p₀ : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x)))
    (y : AlgebraicClosure ℚ) (hy : y ^ p₀ = ((x : L') : AlgebraicClosure ℚ)) :
    ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q ∧
      (∀ z : 𝓞 L', z ∈ v.asIdeal ↔ P.valuation (algebraMap L' (AlgebraicClosure ℚ) z) < 1) ∧
      ∃ σ ∈ P.inertiaSubgroupIn ℚ, (∀ z : L', σ z = z) ∧ σ y ≠ y := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation.solution
