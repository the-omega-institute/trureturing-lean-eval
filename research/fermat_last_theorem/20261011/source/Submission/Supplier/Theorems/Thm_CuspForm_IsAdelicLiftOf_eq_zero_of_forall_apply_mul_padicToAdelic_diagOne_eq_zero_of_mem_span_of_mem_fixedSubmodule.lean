import Submission.Supplier.Definitions.Def_CuspForm_AdelicLift
import Submission.Supplier.Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Submission.Supplier.Definitions.Def_LocalNewvector_ReductionFunctor
import Submission.Supplier.Definitions.Def_NumberField_AdelicLevel
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CuspForm_IsAdelicLiftOf_eq_zero_of_forall_apply_mul_padicToAdelic_diagOne_eq_zero_of_mem_span_of_mem_fixedSubmodule

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
open scoped MatrixGroups ModularForm

theorem CuspForm.IsAdelicLiftOf.eq_zero_of_forall_apply_mul_padicToAdelic_diagOne_eq_zero_of_mem_span_of_mem_fixedSubmodule
    {M' : ℕ} [NeZero M'] (q : ℕ) [Fact q.Prime]
    {g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2}
    {Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hΦg : g.IsAdelicLiftOf Φ)
    (y : LocalNewvector.AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (hfix : y ∈ LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1)
      (LocalNewvector.AdelicSpan Φ))
    (h0 : ∀ (u : ℤ_[q]ˣ) (h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
          LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
            (LocalNewvector.AdelicSpan.toFn Φ y).toFn
                (h * AdelicDock.padicToAdelic q
                  (NumberField.AdelicLevel.diagOne (Units.map PadicInt.Coe.ringHom.toMonoidHom u))) = 0) :
    y = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOf_eq_zero_of_forall_apply_mul_padicToAdelic_diagOne_eq_zero_of_mem_span_of_mem_fixedSubmodule.solution
