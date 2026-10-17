import Submission.Supplier.Definitions.Def_LatticeTreeBaseChange
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_LT_LatticeTree_Vertex_exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

theorem
LT.LatticeTree.Vertex.exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (v x : LT.LatticeTree.Vertex R K) (n : ℕ)
    (h : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) v x)
    (h' : ¬ LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v x) :
    ∃ y : LT.LatticeTree.Vertex R K,
      LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x y ∧
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n v y ∧
          ∀ z : LT.LatticeTree.Vertex R K,
            LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x z → z ≠ x → z ≠ y →
              ¬ LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) v z := by p2m_exact_reverting @_root_.P2MW.S_LT_LatticeTree_Vertex_exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin.solution

#print axioms LT.LatticeTree.Vertex.exists_isWithin_one_and_isWithin_and_forall_not_isWithin_succ_of_isWithin_succ_of_not_isWithin
