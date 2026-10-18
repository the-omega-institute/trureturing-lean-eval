import Submission.Supplier.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Submission.Supplier.Definitions.Def_AutomorphicForm_CuspidalConstituent
import Submission.Supplier.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Submission.Supplier.Definitions.Def_AutomorphicForm_FactorizableTestFn
import Submission.Supplier.Definitions.Def_AutomorphicForm_RightConvolution
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (θ : AdelicGL2 (𝓞 K) K → ℂ) (hθ : IsArchSmoothAt hw θ) (m lam : ℂ)
    (hm : archDerivAt hw .E θ - archDerivAt hw .Fm θ = m • θ)
    (hΩ : archCasimirAt hw θ = lam • θ) :
    let lower : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    let raise : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    (∀ j : ℕ, IsArchSmoothAt hw (lower^[j] θ) ∧
      archDerivAt hw .E (lower^[j] θ) - archDerivAt hw .Fm (lower^[j] θ) = (m - 2 * Complex.I * j) • lower^[j] θ ∧
      archCasimirAt hw (lower^[j] θ) = lam • lower^[j] θ) ∧
    (∀ j : ℕ, IsArchSmoothAt hw (raise^[j] θ) ∧
      archDerivAt hw .E (raise^[j] θ) - archDerivAt hw .Fm (raise^[j] θ) = (m + 2 * Complex.I * j) • raise^[j] θ ∧
      archCasimirAt hw (raise^[j] θ) = lam • raise^[j] θ) ∧
    (∀ M : ℕ, raise^[M] (lower^[M] θ) =
      (∏ j ∈ Finset.range M, (-4 * lam + (m - 2 * Complex.I * j) ^ 2 - 2 * Complex.I * (m - 2 * Complex.I * j))) • θ) ∧
    (∀ M : ℕ, lower^[M] (raise^[M] θ) =
      (∏ j ∈ Finset.range M, (-4 * lam + (m + 2 * Complex.I * j) ^ 2 + 2 * Complex.I * (m + 2 * Complex.I * j))) • θ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul.solution

#print axioms AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul
