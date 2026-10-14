import Mathlib
import Submission.Supplier.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_finite_torsionSubset

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u
theorem GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_finite_torsionSubset
    {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] (L : RelativeGroupLaw k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] (n : ℕ)
    (hfin : (L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap k K))) n).Finite) :
    LocallyQuasiFinite (L.schemeNsmul n) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_finite_torsionSubset.solution
