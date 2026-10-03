import Submission.Presentation

/-! Reconstruction of the presented group from Gardam's four-coset model. -/

namespace Submission.Promislow

noncomputable section

open Coset

def transP (v : Vec) : UnitConjecture.P := px ^ v.x * py ^ v.y * pz ^ v.z

def sigma : Coset → UnitConjecture.P
  | one => 1 | a => pa | b => pb | ab => pa * pb

theorem transP_zero : transP zeroV = 1 := by simp [transP, zeroV]

theorem transP_add (v w : Vec) : transP (addV v w) = transP v * transP w := by
  symm
  calc
    transP v * transP w =
        (px ^ v.x * py ^ v.y) * (pz ^ v.z * px ^ w.x) * py ^ w.y * pz ^ w.z := by
      simp only [transP, mul_assoc]
    _ = (px ^ v.x * py ^ v.y) * (px ^ w.x * pz ^ v.z) * py ^ w.y * pz ^ w.z := by
      rw [(commute_xz.symm.zpow_zpow v.z w.x).eq]
    _ = (px ^ v.x * (py ^ v.y * px ^ w.x)) * (pz ^ v.z * py ^ w.y) * pz ^ w.z := by
      simp only [mul_assoc]
    _ = (px ^ v.x * (px ^ w.x * py ^ v.y)) * (py ^ w.y * pz ^ v.z) * pz ^ w.z := by
      rw [(commute_xy.symm.zpow_zpow v.y w.x).eq,
        (commute_yz.symm.zpow_zpow v.z w.y).eq]
    _ = transP (addV v w) := by simp only [transP, addV, zpow_add, mul_assoc]

theorem action_a (v : Vec) : pa * transP v = transP (rho a v) * pa := by
  have hx : SemiconjBy pa px px := (Commute.refl pa).pow_right 2
  have hy : SemiconjBy pa py py⁻¹ := move_a_y
  have hz : SemiconjBy pa pz pz⁻¹ :=
    (mul_inv_eq_iff_eq_mul).mp (inverse_conjugation pz pa conjugate_z_a)
  have h := ((hx.zpow_right v.x).mul_right (hy.zpow_right v.y)).mul_right
    (hz.zpow_right v.z)
  simpa only [transP, rho, inv_zpow', zpow_neg] using h.eq

theorem action_b (v : Vec) : pb * transP v = transP (rho b v) * pb := by
  have hx : SemiconjBy pb px px⁻¹ :=
    (mul_inv_eq_iff_eq_mul).mp (inverse_conjugation px pb presentation_x)
  have hy : SemiconjBy pb py py := (Commute.refl pb).pow_right 2
  have hz : SemiconjBy pb pz pz⁻¹ :=
    (mul_inv_eq_iff_eq_mul).mp (inverse_conjugation pz pb conjugate_z_b)
  have h := ((hx.zpow_right v.x).mul_right (hy.zpow_right v.y)).mul_right
    (hz.zpow_right v.z)
  simpa only [transP, rho, inv_zpow', zpow_neg] using h.eq

theorem section_action (q : Coset) (v : Vec) :
    sigma q * transP v = transP (rho q v) * sigma q := by
  cases q
  · simp [sigma, rho]
  · exact action_a v
  · exact action_b v
  · change (pa * pb) * transP v = transP (rho ab v) * (pa * pb)
    calc
      (pa * pb) * transP v = pa * (pb * transP v) := mul_assoc _ _ _
      _ = pa * (transP (rho b v) * pb) := by rw [action_b]
      _ = (pa * transP (rho b v)) * pb := (mul_assoc _ _ _).symm
      _ = (transP (rho a (rho b v)) * pa) * pb := by rw [action_a]
      _ = transP (rho ab v) * (pa * pb) := by simp [rho, mul_assoc]

theorem move_b_a : pb * pa = transP (factor b a) * sigma ab := by
  have hb : pb * px = px⁻¹ * pb :=
    (mul_inv_eq_iff_eq_mul).mp (inverse_conjugation px pb presentation_x)
  calc
    pb * pa = (pb * px) * pa⁻¹ := by (try simp only [pow_two]); group
    _ = (px⁻¹ * pb) * pa⁻¹ := by rw [hb]
    _ = transP (factor b a) * sigma ab := by
      simp only [transP, factor, sigma, zpow_neg_one, zpow_one, pow_two]
      group

theorem section_b_ab : sigma b * sigma ab = transP (factor b ab) * sigma a := by
  change pb * (pa * pb) = transP (factor b ab) * pa
  calc
    pb * (pa * pb) = (pb * pa) * pb := (mul_assoc _ _ _).symm
    _ = (transP (factor b a) * sigma ab) * pb := by rw [move_b_a]
    _ = transP (factor b a) * (pa * py) := by simp only [sigma, pow_two, mul_assoc]
    _ = transP (factor b a) * (py⁻¹ * pa) := by rw [move_a_y]
    _ = (transP (factor b a) * transP ⟨0, -1, 0⟩) * pa := by
      simp [transP, mul_assoc]
    _ = transP (addV (factor b a) ⟨0, -1, 0⟩) * pa := by rw [transP_add]
    _ = transP (factor b ab) * pa := rfl

theorem section_ab_a : sigma ab * sigma a = transP (factor ab a) * sigma b := by
  change (pa * pb) * pa = transP (factor ab a) * pb
  calc
    (pa * pb) * pa = pa * (pb * pa) := mul_assoc _ _ _
    _ = pa * (transP (factor b a) * sigma ab) := by rw [move_b_a]
    _ = (pa * transP (factor b a)) * sigma ab := (mul_assoc _ _ _).symm
    _ = (transP (rho a (factor b a)) * pa) * sigma ab := by rw [action_a]
    _ = transP (rho a (factor b a)) * (px * pb) := by simp only [sigma, pow_two, mul_assoc]
    _ = (transP (rho a (factor b a)) * transP ⟨1, 0, 0⟩) * pb := by
      simp [transP, mul_assoc]
    _ = transP (addV (rho a (factor b a)) ⟨1, 0, 0⟩) * pb := by rw [transP_add]
    _ = transP (factor ab a) * pb := rfl

theorem section_mul (q r : Coset) :
    sigma q * sigma r = transP (factor q r) * sigma (addQ q r) := by
  cases q <;> cases r
  all_goals first
    | exact move_b_a
    | exact section_b_ab
    | exact section_ab_a
    | simpa [sigma, factor, addQ, transP, zeroV, pow_two, mul_assoc] using move_a_y

def decodeFun (g : E) : UnitConjecture.P := transP g.v * sigma g.q

theorem decode_mul (g h : E) : decodeFun (g * h) = decodeFun g * decodeFun h := by
  rcases g with ⟨v, q⟩
  rcases h with ⟨w, r⟩
  symm
  calc
    decodeFun ⟨v, q⟩ * decodeFun ⟨w, r⟩ =
        transP v * (sigma q * transP w) * sigma r := by simp [decodeFun, mul_assoc]
    _ = transP v * (transP (rho q w) * sigma q) * sigma r := by rw [section_action]
    _ = (transP v * transP (rho q w)) * (sigma q * sigma r) := by simp only [mul_assoc]
    _ = transP (addV v (rho q w)) * (transP (factor q r) * sigma (addQ q r)) := by
      rw [← transP_add, section_mul]
    _ = decodeFun (⟨v, q⟩ * ⟨w, r⟩) := by
      simp only [decodeFun, mul_def, mulE, ← transP_add, ← mul_assoc]

def decode : E →* UnitConjecture.P where
  toFun := decodeFun
  map_one' := by simp [decodeFun, one_def, oneE, transP_zero, sigma]
  map_mul' := decode_mul

@[simp] theorem encode_a : encode pa = ea := PresentedGroup.toGroup.of relations_satisfied
@[simp] theorem encode_b : encode pb = eb := PresentedGroup.toGroup.of relations_satisfied

theorem encode_x : encode px = ⟨⟨1, 0, 0⟩, one⟩ := by
  rw [map_pow, encode_a]
  decide

theorem encode_y : encode py = ⟨⟨0, 1, 0⟩, one⟩ := by
  rw [map_pow, encode_b]
  decide

theorem encode_z : encode pz = ⟨⟨0, 0, 1⟩, one⟩ := by
  rw [map_pow, map_mul, encode_a, encode_b]
  decide

theorem encode_trans (v : Vec) : encode (transP v) = ⟨v, one⟩ := by
  simp only [transP, map_mul, map_zpow, encode_x, encode_y, encode_z, translation_zpow,
    mul_def]
  apply E.ext
  · apply Vec.ext <;> simp [mulE, addV, rho, factor, zeroV, scaleZ, addQ]
  · rfl

theorem encode_section (q : Coset) : encode (sigma q) = ⟨zeroV, q⟩ := by
  cases q <;> simp [sigma, ea, eb, mulE, rho, addV, zeroV, factor, addQ, oneE]

theorem decode_encode (g : UnitConjecture.P) : decode (encode g) = g := by
  have h : decode.comp encode = MonoidHom.id UnitConjecture.P := by
    apply PresentedGroup.ext
    intro t
    change decode (encode (PresentedGroup.of t)) = PresentedGroup.of t
    cases t
    · change decode (encode pa) = pa
      rw [encode_a]
      change transP zeroV * sigma a = pa
      simp [transP_zero, sigma]
    · change decode (encode pb) = pb
      rw [encode_b]
      change transP zeroV * sigma b = pb
      simp [transP_zero, sigma]
  exact DFunLike.congr_fun h g

theorem encode_decode (g : E) : encode (decode g) = g := by
  change encode (transP g.v * sigma g.q) = g
  rw [map_mul, encode_trans, encode_section, mul_def]
  rcases g with ⟨v, q⟩
  cases q <;> apply E.ext
  all_goals first | rfl | apply Vec.ext <;> simp [mulE, rho, addV, zeroV, factor, addQ]

/-- Both inverse identities certify faithfulness of the four-coset coordinates. -/
def normalEquiv : UnitConjecture.P ≃* E where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode
  map_mul' := encode.map_mul

theorem presented_torsion_free (g : UnitConjecture.P) (n : ℕ) (hn : n ≠ 0)
    (h : g ^ n = 1) : g = 1 := by
  apply normalEquiv.injective
  apply torsion_free (encode g) n hn
  simpa only [map_pow, map_one] using congrArg encode h

end

end Submission.Promislow
