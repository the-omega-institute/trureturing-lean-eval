import Submission.Supplier.Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Submission.Supplier.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_submission FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_submission FixedPoints.instAddCommMonoidElemFixedPoints_submission
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (W : AdelicGL2 (𝓞 F) F → ℂ)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), W (unipotentGL2 u * g) = ψ u * W g)
    (hZ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      W (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ i j : Fin 2,
      ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
        ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v)
    (hW : W g₀ ≠ 0) :
    ∃ (t : (AdeleRing (𝓞 F) F)ˣ) (k : AdelicGL2 (𝓞 F) F),
      k ∈ maximalCompactAt F S ∧
      (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1) ∧
      W (diagOne t * k) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero.solution

#print axioms AutomorphicForm.exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero
