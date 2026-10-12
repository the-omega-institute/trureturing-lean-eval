import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_M4aHerbrand_finrank_sUnit_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
open IsDedekindDomain NumberField

theorem M4aHerbrand.finrank_sUnit_eq (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    Module.Finite ℤ (Additive (S.unit K)) ∧
    Module.finrank ℤ (Additive (S.unit K)) = Nat.card S + NumberField.Units.rank K := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_finrank_sUnit_eq.solution
