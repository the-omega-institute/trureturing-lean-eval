import Submission.NormalForm
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Commute.Basic

/-! Presentation calculations for Gardam's §3.1 normal form. -/

namespace Submission.Promislow

noncomputable section

abbrev pa : UnitConjecture.P := PresentedGroup.of UnitConjecture.generators.a
abbrev pb : UnitConjecture.P := PresentedGroup.of UnitConjecture.generators.b
abbrev px : UnitConjecture.P := pa ^ 2
abbrev py : UnitConjecture.P := pb ^ 2
abbrev pz : UnitConjecture.P := (pa * pb) ^ 2

theorem presentation_x : pb⁻¹ * px * pb = px⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  change PresentedGroup.mk UnitConjecture.relations
    (UnitConjecture.b⁻¹ * UnitConjecture.a ^ 2 * UnitConjecture.b * UnitConjecture.a ^ 2) = 1
  exact PresentedGroup.one_of_mem (by simp [UnitConjecture.relations])

theorem presentation_y : pa⁻¹ * py * pa = py⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  change PresentedGroup.mk UnitConjecture.relations
    (UnitConjecture.a⁻¹ * UnitConjecture.b ^ 2 * UnitConjecture.a * UnitConjecture.b ^ 2) = 1
  exact PresentedGroup.one_of_mem (by simp [UnitConjecture.relations])

theorem inverse_conjugation {G : Type*} [Group G] (g t : G)
    (h : t⁻¹ * g * t = g⁻¹) : t * g * t⁻¹ = g⁻¹ := by
  have hi := congrArg Inv.inv h
  simp only [mul_inv_rev, inv_inv, ← mul_assoc] at hi
  calc
    t * g * t⁻¹ = t * (t⁻¹ * g⁻¹ * t) * t⁻¹ := by rw [hi]
    _ = g⁻¹ := by group

theorem inversion_commutes_square {G : Type*} [Group G] (g t : G)
    (h : t⁻¹ * g * t = g⁻¹) : Commute g (t ^ 2) := by
  have hl := inverse_conjugation g t h
  have hc : t * (t * g * t⁻¹) * t⁻¹ = g := by
    rw [hl]
    have hi := congrArg Inv.inv hl
    simpa only [mul_inv_rev, inv_inv, ← mul_assoc] using hi
  change g * t ^ 2 = t ^ 2 * g
  calc
    g * t ^ 2 = (t * (t * g * t⁻¹) * t⁻¹) * t ^ 2 := by rw [hc]
    _ = t ^ 2 * g := by (try simp only [pow_two]); group

theorem commute_xy : Commute px py := inversion_commutes_square px pb presentation_x

theorem move_x_b : px * pb = pb * px⁻¹ := by
  apply (inv_mul_eq_iff_eq_mul).mp
  simpa only [mul_assoc] using presentation_x

theorem move_a_y : pa * py = py⁻¹ * pa := by
  exact (mul_inv_eq_iff_eq_mul).mp (inverse_conjugation py pa presentation_y)

theorem conjugate_z_a : pa⁻¹ * pz * pa = pz⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  calc
    pa⁻¹ * pz * pa * pz = pb * pa * pb * (px * pb) * pa * pb := by (try simp only [pow_two]); group
    _ = pb * pa * pb * (pb * px⁻¹) * pa * pb := by rw [move_x_b]
    _ = pb * (pa * py) * pa⁻¹ * pb := by (try simp only [pow_two]); group
    _ = pb * (py⁻¹ * pa) * pa⁻¹ * pb := by rw [move_a_y]
    _ = 1 := by (try simp only [pow_two]); group

theorem conjugate_z_b : pb⁻¹ * pz * pb = pz⁻¹ := by
  have hz : (pa * pb)⁻¹ * pz * (pa * pb) = pz := by (try simp only [pow_two]); group
  have ha := inverse_conjugation pz pa conjugate_z_a
  calc
    pb⁻¹ * pz * pb = (pa * pb)⁻¹ * (pa * pz * pa⁻¹) * (pa * pb) := by (try simp only [pow_two]); group
    _ = (pa * pb)⁻¹ * pz⁻¹ * (pa * pb) := by rw [ha]
    _ = ((pa * pb)⁻¹ * pz * (pa * pb))⁻¹ := by (try simp only [pow_two]); group
    _ = pz⁻¹ := by rw [hz]

theorem commute_xz : Commute px pz := by
  have h : Commute pz px := inversion_commutes_square pz pa conjugate_z_a
  exact h.symm

theorem commute_yz : Commute py pz := by
  have h : Commute pz py := inversion_commutes_square pz pb conjugate_z_b
  exact h.symm

end

end Submission.Promislow
