import Submission.Supplier.Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_exists_maximalCompactAway_subset_of_mem_nhds_one

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm Filter Topology

theorem AutomorphicForm.exists_maximalCompactAway_subset_of_mem_nhds_one
    (F : Type) [Field F] [NumberField F]
    (W : Set (AdelicGL2 (𝓞 F) F)) (_hW : W ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
      (maximalCompactAway F S₀ : Set (AdelicGL2 (𝓞 F) F)) ⊆ W := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_maximalCompactAway_subset_of_mem_nhds_one.solution

#print axioms AutomorphicForm.exists_maximalCompactAway_subset_of_mem_nhds_one
