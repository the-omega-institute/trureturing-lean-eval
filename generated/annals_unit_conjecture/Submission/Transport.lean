import Submission.Reconstruction
import Submission.Support

/-! Transport of the exact official coefficients through the faithful normal form. -/

namespace Submission.Promislow

noncomputable section

def algebraEquiv : UnitConjecture.R ≃+* RE :=
  MonoidAlgebra.mapDomainRingEquiv (ZMod 2) normalEquiv

@[simp] theorem algebra_coe (g : UnitConjecture.P) :
    algebraEquiv (g : UnitConjecture.R) = basis (encode g) := by
  change MonoidAlgebra.mapDomainRingEquiv (ZMod 2) normalEquiv
    (MonoidAlgebra.single g 1) = MonoidAlgebra.single (normalEquiv g) 1
  exact MonoidAlgebra.mapDomainRingEquiv_single normalEquiv 1 g

theorem official_x : UnitConjecture.x = px := rfl
theorem official_y : UnitConjecture.y = py := rfl
theorem official_z : UnitConjecture.z = pz := rfl

theorem image_u : algebraEquiv UnitConjecture.u = unitE := by
  have ha : (UnitConjecture.a : UnitConjecture.P) = pa := rfl
  have hb : (UnitConjecture.b : UnitConjecture.P) = pb := rfl
  simp only [UnitConjecture.u, UnitConjecture.p, UnitConjecture.q, UnitConjecture.r,
    UnitConjecture.s, map_add, map_mul, map_one, algebra_coe, official_x, official_y,
    official_z, map_inv, encode_x, encode_y, encode_z, ha, hb, encode_a, encode_b,
    unitE, polyP, polyQ, polyR, polyS, ex, ey, ez]
  simp [basis, MonoidAlgebra.single_mul_single]

theorem official_isUnit : IsUnit UnitConjecture.u := by
  refine isUnit_iff_exists.mpr ⟨algebraEquiv.symm inverseE, ?_, ?_⟩
  · apply algebraEquiv.injective
    simpa only [map_mul, map_one, RingEquiv.apply_symm_apply, image_u] using mul_inverseE
  · apply algebraEquiv.injective
    simpa only [map_mul, map_one, RingEquiv.apply_symm_apply, image_u] using inverseE_mul

theorem official_not_basis : ¬ ∃ g : UnitConjecture.P, UnitConjecture.u = g := by
  rintro ⟨g, hg⟩
  apply unitE_not_basis (encode g)
  simpa only [image_u, algebra_coe] using congrArg algebraEquiv hg

end
end Submission.Promislow
