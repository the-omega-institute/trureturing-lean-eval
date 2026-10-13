import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
    (F : Type) [Field F] [NumberField F] {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt.solution
