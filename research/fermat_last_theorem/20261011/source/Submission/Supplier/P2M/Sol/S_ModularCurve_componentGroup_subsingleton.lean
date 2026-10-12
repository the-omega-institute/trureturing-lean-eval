import Submission.Supplier.Definitions.Def_ModularCurve_ComponentGroup
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_ModularCurve_componentGroup_subsingleton

open ModularCurve Finset

private theorem aux_charLat_subsingleton {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 1) :
    Subsingleton (characterLattice ι) := by
  constructor
  rintro ⟨D, hD⟩ ⟨D', hD'⟩
  rw [mem_characterLattice] at hD hD'
  ext x
  have hx : ∀ y : ι, y = x := fun y => Fintype.card_le_one_iff.mp hι y x
  have hsum : ∀ E : ι → ℤ, ∑ y : ι, E y = E x := fun E => by
    rw [Finset.sum_eq_single x (fun y _ hy => absurd (hx y) hy)
        (fun h => absurd (Finset.mem_univ x) h)]
  simp only [hsum] at hD hD'
  simp [hD, hD']

theorem solution {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 1) (e : ι → ℕ) :
    Subsingleton (componentGroup e) := by
  have h𝒳 := aux_charLat_subsingleton (ι := ι) hι
  have hdual : Subsingleton (Module.Dual ℤ (characterLattice ι)) :=
    ⟨fun φ ψ => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  exact Quotient.instSubsingletonQuotient _
