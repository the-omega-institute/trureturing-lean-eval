/-
Copyright (c) 2026. Released under Apache 2.0.
The genuine last-vertex simplex operator on a composable string of simplices.
Uses Joël Riou's Mathlib composable-arrow nerve and the simplex category,
released under Apache-2.0. This is the operator needed to compare the actual
singular-simplex nerve with the protected singular simplicial set.
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open scoped Simplicial

namespace CWComparison

/-- The last vertex of every simplex in a string, transported to its final
simplex, defines an actual monotone simplex operator. -/
def lastVertexOperator {n : ℕ} (c : ComposableArrows SimplexCategory n) :
    ⦋n⦌ ⟶ c.obj (Fin.last n) :=
  SimplexCategory.Hom.mk {
    toFun := fun i => (c.map (homOfLE (Fin.le_last i))).toOrderHom
      (Fin.last (c.obj i).len)
    monotone' := by
      intro i j hij
      dsimp only
      have hcomp : c.map (homOfLE (Fin.le_last i)) =
          c.map (homOfLE hij) ≫ c.map (homOfLE (Fin.le_last j)) :=
        c.map_comp _ _
      rw [hcomp, SimplexCategory.comp_toOrderHom]
      exact (c.map (homOfLE (Fin.le_last j))).toOrderHom.monotone (Fin.le_last _) }

/-- Restricting a string by any simplex operator commutes with its last-vertex
operator after the actual map from the new final simplex to the old one. -/
theorem lastVertexOperator_whisker {m n : SimplexCategory} (f : m ⟶ n)
    (c : ComposableArrows SimplexCategory n.len) :
    lastVertexOperator (c.whiskerLeft f.toOrderHom.monotone.functor) ≫
        c.map (homOfLE (Fin.le_last (f.toOrderHom (Fin.last m.len)))) =
      f ≫ lastVertexOperator c := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  change (c.map (homOfLE (Fin.le_last (f.toOrderHom (Fin.last m.len))))).toOrderHom
      ((c.map (homOfLE (f.toOrderHom.monotone (Fin.le_last i)))).toOrderHom
        (Fin.last (c.obj (f.toOrderHom i)).len)) =
    (c.map (homOfLE (Fin.le_last (f.toOrderHom i)))).toOrderHom
      (Fin.last (c.obj (f.toOrderHom i)).len)
  exact (congrArg (fun (a : c.obj (f.toOrderHom i) ⟶ c.obj (Fin.last n.len)) =>
    a.toOrderHom (Fin.last (c.obj (f.toOrderHom i)).len))
      (c.map_comp
        (homOfLE (f.toOrderHom.monotone (Fin.le_last i)))
        (homOfLE (Fin.le_last (f.toOrderHom (Fin.last m.len)))))).symm

end CWComparison
