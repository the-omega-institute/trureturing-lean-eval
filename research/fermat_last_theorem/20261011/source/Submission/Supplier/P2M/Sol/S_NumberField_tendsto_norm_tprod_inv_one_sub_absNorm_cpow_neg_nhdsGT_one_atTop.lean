import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_NumberField_tendsto_norm_tprod_inv_one_sub_absNorm_cpow_neg_nhdsGT_one_atTop

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open NumberField Filter Complex IsDedekindDomain
open scoped Topology Classical BigOperators

theorem solution (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    Tendsto
      (fun σ : ℝ => ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖)
      (𝓝[>] 1) atTop := by
  exact _root_.P2MW.S_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one.Ws41.EulerZeta.tendsto_norm_tprod_atTop K T

end P2MW.S_NumberField_tendsto_norm_tprod_inv_one_sub_absNorm_cpow_neg_nhdsGT_one_atTop

#print axioms _root_.P2MW.S_NumberField_tendsto_norm_tprod_inv_one_sub_absNorm_cpow_neg_nhdsGT_one_atTop.solution
