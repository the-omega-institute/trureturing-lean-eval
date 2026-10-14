import Submission.Supplier.Definitions.Def_AutomorphicForm_ConstantTerm
import Submission.Supplier.Definitions.Def_NumberField_StandardGlobalAddCharRat
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_LocalFunctionSpace_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

theorem AutomorphicForm.LocalFunctionSpace.exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (S : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hstab : ∀ U ∈ S, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => U (g * k)) ∈ S)
    (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hW : W ∈ S)
    (hsmW : ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
    (a₀ : p.adicCompletion ℚ) (δ : (WithZero (Multiplicative ℤ))ˣ) :
    ∃ W' ∈ S, ∀ t : GL (Fin 2) (p.adicCompletion ℚ),
      (t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 = 1 →
      (Valued.v ((t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 - a₀) < (δ : WithZero (Multiplicative ℤ)) →
        (fun g => W' (g * t)) - (fun g => W (g * t)) ∈ Submodule.span ℂ
        {V : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ U ∈ S, ∃ x : p.adicCompletion ℚ,
          V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - NumberField.StandardAddChar.psiV p x • U}) ∧
      (¬ Valued.v ((t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 - a₀) < (δ : WithZero (Multiplicative ℤ)) →
        (fun g => W' (g * t)) ∈ Submodule.span ℂ
        {V : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ U ∈ S, ∃ x : p.adicCompletion ℚ,
          V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - NumberField.StandardAddChar.psiV p x • U}) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_LocalFunctionSpace_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span.solution
