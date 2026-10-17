import Mathlib
import Submission.Supplier.Definitions.Def_ExtEndgame_ProductionDatum
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousH2
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousH2Map
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousH1
import Submission.Supplier.Definitions.Def_GroupCohomology_CupProduct
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousDuality
import Submission.Supplier.Definitions.Def_GroupCohomology_Selmer
import Submission.Supplier.Definitions.Def_DualSelmer_ExtConditions
import Submission.Supplier.Definitions.Def_ExtCitation_KummerBridge
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_groupCohomology_bijective_theta_dualTwist_of_res_of_isOpen

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

private local instance scalarAddCommGroup (p : ℕ) : AddCommGroup (ZMod p) :=
  (inferInstance : CommRing (ZMod p)).toAddCommGroup
theorem groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q)) (U : Subgroup S) [U.FiniteIndex] (hUp : IsUnit ((U.index : ℕ) : ZMod p))
    (hU : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap ((primeLocalToGlobal q).comp S.subtype) ≤ U)
    (hTU : FiniteDimensional (ZMod p) (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) ∧
      finrank (ZMod p) (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) = 1)
    (M : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → M.ρ s m = m)
    (inv : continuousH2 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) →ₗ[ZMod p] ZMod p)
    (hinv : Function.Bijective inv)
    (hres : ∀ (invU : continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) →ₗ[ZMod p] ZMod p),
      Function.Bijective invU →
      ∀ (θ₀ : (Rep.res U.subtype M).ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))),
        IsTheta0 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₀ →
      ∀ (θ₁ : continuousH1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (continuousH1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))),
        IsTheta1 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₁ →
      ∀ (θ₂ : continuousH2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Rep.res U.subtype M) →ₗ[ZMod p] Module.Dual (ZMod p)
          (Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))).ρ.invariants),
        IsTheta2 (((primeLocalToGlobal q).comp S.subtype).comp U.subtype) (Module.Dual.eval (ZMod p) M : Rep.res U.subtype M →ₗ[ZMod p]
            Rep.res U.subtype (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)) →ₗ[ZMod p]
            Rep.res U.subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))) invU θ₂ →
      Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂)
    (θ₀ : M.ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₀ : IsTheta0 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₀)
    (θ₁ : continuousH1 ((primeLocalToGlobal q).comp S.subtype) M →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH1 ((primeLocalToGlobal q).comp S.subtype) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₁ : IsTheta1 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₁)
    (θ₂ : continuousH2 ((primeLocalToGlobal q).comp S.subtype) M →ₗ[ZMod p] Module.Dual (ZMod p) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants)
    (hθ₂ : IsTheta2 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₂) :
    Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_bijective_theta_dualTwist_of_res_of_isOpen.solution

#print axioms groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen
