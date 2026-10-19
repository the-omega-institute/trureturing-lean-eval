import Mathlib.RingTheory.Regular.RegularSequence
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_RingTheory_Sequence_isWeaklyRegular_ofFn_of_isWeaklyRegular_ofFn_of_forall_mem_span

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

universe u v
theorem RingTheory.Sequence.isWeaklyRegular_ofFn_of_isWeaklyRegular_ofFn_of_forall_mem_span
    {P : Type u} [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    {M : Type v} [AddCommGroup M] [Module P M] [Module.Finite P M]
    {n : ℕ} (f y : Fin n → P)
    (hy : RingTheory.Sequence.IsWeaklyRegular M (List.ofFn y))
    (hyf : ∀ k, y k ∈ Ideal.span (Set.range f))
    (hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal P) :
    RingTheory.Sequence.IsWeaklyRegular M (List.ofFn f) := by p2m_exact_reverting @_root_.P2MW.S_RingTheory_Sequence_isWeaklyRegular_ofFn_of_isWeaklyRegular_ofFn_of_forall_mem_span.solution
