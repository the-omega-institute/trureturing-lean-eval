import Mathlib
import Submission.Supplier.Definitions.Def_GroupCohomology_TateCohomology
import Submission.Supplier.Definitions.Def_GroupCohomology_TateSeam
import Submission.Supplier.Definitions.Def_GroupCohomology_TateShiftMaps
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Rep_tateDelta_naturality

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.tateDelta_naturality {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X Y : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (hY : Y.ShortExact) (τ : X ⟶ Y) (n : ℤ) :
    Rep.tateδ hX n ≫ Rep.tateMap τ.τ₁ (n + 1) = Rep.tateMap τ.τ₃ n ≫ Rep.tateδ hY n := by p2m_exact_reverting @_root_.P2MW.S_Rep_tateDelta_naturality.solution
