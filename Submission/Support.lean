import Submission.UnitCertificate

/-! The 21 distinct terms in Gardam's unit. -/

namespace Submission.Promislow

noncomputable section

open Coset

def supportE : Finset E :=
  {⟨⟨0, 0, 0⟩, one⟩, ⟨⟨1, 0, 0⟩, one⟩,
   ⟨⟨0, 1, 0⟩, one⟩, ⟨⟨1, 1, 0⟩, one⟩,
   ⟨⟨0, 0, -1⟩, one⟩, ⟨⟨1, 0, -1⟩, one⟩,
   ⟨⟨0, 1, -1⟩, one⟩, ⟨⟨1, 1, -1⟩, one⟩,
   ⟨⟨-1, -1, 0⟩, a⟩, ⟨⟨1, 0, 0⟩, a⟩,
   ⟨⟨0, -1, 1⟩, a⟩, ⟨⟨0, 0, 1⟩, a⟩,
   ⟨⟨0, 0, 0⟩, b⟩, ⟨⟨1, 0, 0⟩, b⟩,
   ⟨⟨0, -1, 1⟩, b⟩, ⟨⟨1, 1, 1⟩, b⟩,
   ⟨⟨0, 0, 0⟩, ab⟩, ⟨⟨1, 0, -1⟩, ab⟩,
   ⟨⟨-1, 0, -1⟩, ab⟩, ⟨⟨0, 1, -1⟩, ab⟩, ⟨⟨0, -1, -1⟩, ab⟩}

theorem supportE_card : supportE.card = 21 := by decide

theorem unitE_as_sum : unitE = ∑ g ∈ supportE, basis g := by
  classical
  simp [supportE, unitE, polyP, polyQ, polyR, polyS, basis, mul_add, add_mul,
    MonoidAlgebra.single_mul_single, MonoidAlgebra.one_def, mul_def, inv_def, one_def,
    mulE, invE, oneE, ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  abel

theorem unitE_coeff (g : E) : unitE.coeff g = if g ∈ supportE then 1 else 0 := by
  classical
  rw [unitE_as_sum]
  simp [basis, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem unitE_support : unitE.coeff.support = supportE := by
  classical
  ext g
  rw [Finsupp.mem_support_iff, unitE_coeff]
  by_cases hg : g ∈ supportE <;> simp [hg]

theorem unitE_support_card : unitE.coeff.support.card = 21 := by
  rw [unitE_support, supportE_card]

theorem unitE_not_basis (g : E) : unitE ≠ basis g := by
  intro h
  have hc := unitE_support_card
  rw [h] at hc
  have hs : (basis g).coeff.support = {g} := by
    simp [basis, MonoidAlgebra.coeff_single]
  rw [hs] at hc
  norm_num at hc

end
end Submission.Promislow
