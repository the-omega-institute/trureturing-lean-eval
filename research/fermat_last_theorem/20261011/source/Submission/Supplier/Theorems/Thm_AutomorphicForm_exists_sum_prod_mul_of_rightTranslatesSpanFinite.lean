import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Data.Complex.Basic
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_exists_sum_prod_mul_of_rightTranslatesSpanFinite

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem AutomorphicForm.exists_sum_prod_mul_of_rightTranslatesSpanFinite
    {G : Type*} [Group G] {n : ℕ} (K : Fin n → Subgroup G)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, Commute x y)
    (f : G → ℂ)
    (hf : ∀ i, ∃ s : Finset (G → ℂ), ∀ k ∈ K i,
      (fun x => f (x * k)) ∈ Submodule.span ℂ (s : Set (G → ℂ))) :
    ∃ (N : ℕ) (a : Fin N → Fin n → G → ℂ) (b : Fin N → G → ℂ),
      (∀ m i, a m i ∈ Submodule.span ℂ
          {ψ : G → ℂ | ∃ x h : G, h ∈ (⨆ j, K j : Subgroup G) ∧ ψ = fun g => f (x * g * h)}) ∧
      (∀ m i, ∃ t : Finset (G → ℂ), ∀ k' ∈ K i,
          (fun g => a m i (g * k')) ∈ Submodule.span ℂ (t : Set (G → ℂ))) ∧
      (∀ m, b m ∈ Submodule.span ℂ
          {ψ : G → ℂ | ∃ h : G, h ∈ (⨆ j, K j : Subgroup G) ∧ ψ = fun x => f (x * h)}) ∧
      ∀ (x : G) (k : Fin n → G), (∀ i, k i ∈ K i) →
        f (x * (List.ofFn k).prod) = ∑ m, (∏ i, a m i (k i)) * b m x := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_sum_prod_mul_of_rightTranslatesSpanFinite.solution
