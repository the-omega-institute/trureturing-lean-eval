import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Matrix_exists_generalLinearGroup_forall_mem_addSubgroup_iff_of_isPrincipalIdealRing

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

theorem Matrix.exists_generalLinearGroup_forall_mem_addSubgroup_iff_of_isPrincipalIdealRing
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (L : AddSubgroup (Matrix n n K))
    (hmul : ∀ x ∈ L, ∀ m : Matrix n n R, x * m.map (algebraMap R K) ∈ L)
    (hbdd : ∃ d : R, d ≠ 0 ∧ ∀ x ∈ L, ∀ i j, algebraMap R K d * x i j ∈ (algebraMap R K).range)
    (hfull : ∃ N : R, N ≠ 0 ∧ ∀ m : Matrix n n R, algebraMap R K N • m.map (algebraMap R K) ∈ L) :
    ∃ g : GL n K, ∀ x : Matrix n n K,
      x ∈ L ↔ ∀ i j, (((g⁻¹ : GL n K) : Matrix n n K) * x) i j ∈ (algebraMap R K).range := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_generalLinearGroup_forall_mem_addSubgroup_iff_of_isPrincipalIdealRing.solution
