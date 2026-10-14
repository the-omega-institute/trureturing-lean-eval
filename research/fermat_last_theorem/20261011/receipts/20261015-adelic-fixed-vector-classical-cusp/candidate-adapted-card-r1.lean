import Submission.Supplier.Definitions.Def_CuspForm_AdelicLift
import Submission.Supplier.Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Submission.Supplier.Definitions.Def_LocalNewvector_ReductionFunctor
import Submission.Supplier.Definitions.Def_NumberField_AdelicLevel
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CuspForm_IsAdelicLiftOf_exists_cuspForm_gamma_inf_gamma0_apply_mul_padicToAdelic_diagOne_eq_slash_of_mem_span_of_mem_fixedSubmodule

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-simp] AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val

set_option autoImplicit false
open scoped MatrixGroups ModularForm

theorem CuspForm.IsAdelicLiftOf.exists_cuspForm_gamma_inf_gamma0_apply_mul_padicToAdelic_diagOne_eq_slash_of_mem_span_of_mem_fixedSubmodule
    {M' : ℕ} [NeZero M'] (q : ℕ) [Fact q.Prime]
    {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (y : LocalNewvector.AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (hfix : y ∈ LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1)
      (LocalNewvector.AdelicSpan Φ))
    (u : ℤ_[q]ˣ) :
    ∃ F : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2,
      ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
          LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
            (LocalNewvector.AdelicSpan.toFn Φ y).toFn
                (h * AdelicDock.padicToAdelic q
                  (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u))) =
              ((⇑F) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOf_exists_cuspForm_gamma_inf_gamma0_apply_mul_padicToAdelic_diagOne_eq_slash_of_mem_span_of_mem_fixedSubmodule.solution

#print axioms CuspForm.IsAdelicLiftOf.exists_cuspForm_gamma_inf_gamma0_apply_mul_padicToAdelic_diagOne_eq_slash_of_mem_span_of_mem_fixedSubmodule
