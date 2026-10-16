import Submission.Supplier.Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Submission.Supplier.Definitions.Def_QuaternionAlgebra_EichlerOrder
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CerednikDrinfeld_jointDelta_zero_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_sub_of_mem_primeHeckeSet

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.jointDelta_zero_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_sub_of_mem_primeHeckeSet
    (N q q' : ℕ) [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqq' : q' ≠ q) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    {a b : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (hn : IsEichlerOrder (meetOrder R n) (N * q)) (hnH : n ∈ primeHeckeSet R q)
    (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ) :
    jointDelta (classSetDegeneracyData R n) 0 ((classSetEdgeHecke N q Λ R n ⟨q, Fact.out⟩).mulVecLin x) =
      (classSetVertexHecke N Λ R ⟨q, Fact.out⟩).mulVecLin (jointDelta (classSetDegeneracyData R n) 0 x) -
        jointDelta (classSetDegeneracyData R n) 1 x := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_jointDelta_zero_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_sub_of_mem_primeHeckeSet.solution
