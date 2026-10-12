import Definitions.Def_FLTPrelim_Ramification
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.GoingUp
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation

open P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation.WtTF.RB
open scoped P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation.WtTF.RB

namespace P2MW.S_ValuationSubring_exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation

open NumberField IsDedekindDomain

set_option autoImplicit false

open NumberField IsDedekindDomain IntermediateField

open scoped Pointwise

namespace WtTF
namespace RB

local notation "ℚ̄" => AlgebraicClosure ℚ

private theorem mem_iff_valuation_lt_one (𝔓 : Ideal (𝓞 ℚ̄)) [𝔓.IsPrime] (P : ValuationSubring ℚ̄)
    (hPmem : ∀ α : ℚ̄, α ∈ P ↔ ∃ a s : 𝓞 ℚ̄, s ∉ 𝔓 ∧ α = (a : ℚ̄) * (s : ℚ̄)⁻¹)
    (w : 𝓞 ℚ̄) : w ∈ 𝔓 ↔ P.valuation (w : ℚ̄) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
  constructor
  · intro hw
    by_cases hw0 : (w : ℚ̄) = 0
    · exact Or.inl hw0
    · right
      intro hinv
      obtain ⟨a, s, hs, heq⟩ := (hPmem _).mp hinv
      have hsne : (s : ℚ̄) ≠ 0 := coe_ne_zero_of_notMem hs
      have h2 : (s : ℚ̄) = (w : ℚ̄) * a := by
        calc (s : ℚ̄) = (w : ℚ̄) * ((w : ℚ̄)⁻¹ * s) := by rw [mul_inv_cancel_left₀ hw0]
          _ = (w : ℚ̄) * ((a : ℚ̄) * (s : ℚ̄)⁻¹ * s) := by rw [← heq]
          _ = (w : ℚ̄) * a := by rw [inv_mul_cancel_right₀ hsne]
      have h3 : s = w * a := by
        apply NumberField.RingOfIntegers.coe_injective
        rw [map_mul]
        exact h2
      exact hs (h3 ▸ Ideal.mul_mem_right a 𝔓 hw)
  · rintro (hw0 | hinv)
    · have hw : w = 0 := NumberField.RingOfIntegers.coe_injective (hw0.trans (map_zero _).symm)
      rw [hw]
      exact 𝔓.zero_mem
    · by_contra hw
      apply hinv
      exact (hPmem _).mpr ⟨1, w, hw, by
        rw [show ((1 : 𝓞 ℚ̄) : ℚ̄) = 1 from map_one _, one_mul]⟩

private theorem pin_of_under_eq (L' : IntermediateField ℚ ℚ̄) [NumberField L']
    (v : HeightOneSpectrum (𝓞 L')) (𝔓 : Ideal (𝓞 ℚ̄)) [𝔓.IsPrime]
    (h𝔓L' : 𝔓.under (𝓞 L') = v.asIdeal) (P : ValuationSubring ℚ̄)
    (hPmem : ∀ α : ℚ̄, α ∈ P ↔ ∃ a s : 𝓞 ℚ̄, s ∉ 𝔓 ∧ α = (a : ℚ̄) * (s : ℚ̄)⁻¹) :
    ∀ z : 𝓞 L', z ∈ v.asIdeal ↔ P.valuation (algebraMap L' ℚ̄ z) < 1 := by
  intro z
  rw [← h𝔓L', ← coe_ringOfIntegersMap (F₂ := ℚ̄) z]
  exact mem_iff_valuation_lt_one 𝔓 P hPmem (algebraMap (𝓞 L') (𝓞 ℚ̄) z)

end RB
p2m_reactivate "P2MW.S_ValuationSubring_exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation.WtTF.RB"

local notation "ℚ̄" => AlgebraicClosure ℚ

set_option maxHeartbeats 6400000 in
open RB in

private theorem exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd
    (L' : IntermediateField ℚ ℚ̄) [NumberField L']
    (p₀ : ℕ) (hp₀ : p₀.Prime) (x : (L' : Type)ˣ) (v : HeightOneSpectrum (𝓞 L'))
    (q : ℕ) (hq : q.Prime) (hqv : (q : 𝓞 L') ∈ v.asIdeal)
    (hv : ¬ ((p₀ : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x)))
    (y : ℚ̄) (hy : y ^ p₀ = ((x : L') : ℚ̄)) :
    ∃ P : ValuationSubring ℚ̄, P.LiesOverPrime q ∧
      (∀ z : 𝓞 L', z ∈ v.asIdeal ↔ P.valuation (algebraMap L' (AlgebraicClosure ℚ) z) < 1) ∧
      ∃ σ ∈ P.inertiaSubgroupIn ℚ, (∀ z : L', σ z = z) ∧ σ y ≠ y := by
  classical
  have := isAlgebraic_rat_qbar

  have hcoL : ∀ z : ↥L', (z : ℚ̄) = algebraMap (↥L') ℚ̄ z := fun z => rfl
  have hx0 : ((x : ↥L') : ℚ̄) ≠ 0 := by
    rw [hcoL]
    exact (map_ne_zero_iff _ (algebraMap (↥L') ℚ̄).injective).mpr x.ne_zero
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hp₀.ne_zero] at hy
    exact hx0 hy.symm
  have haval : Polynomial.aeval y (Polynomial.X ^ p₀ - Polynomial.C (x : ↥L')) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hy, hcoL, sub_self]
  have hyint : IsIntegral (↥L') y := by
    refine ⟨Polynomial.X ^ p₀ - Polynomial.C (x : ↥L'),
      Polynomial.monic_X_pow_sub_C _ hp₀.ne_zero, ?_⟩
    rw [← Polynomial.aeval_def]
    exact haval
  set L'' : IntermediateField (↥L') ℚ̄ := (↥L')⟮y⟯ with hL''def
  have : FiniteDimensional (↥L') ↥L'' := IntermediateField.adjoin.finiteDimensional hyint
  have : NumberField ↥L'' := NumberField.of_module_finite (↥L') ↥L''
  have hyL'' : y ∈ L'' := IntermediateField.mem_adjoin_simple_self (↥L') y
  obtain ⟨yt, hytcoe⟩ : ∃ yt : ↥L'', (yt : ℚ̄) = y := ⟨⟨y, hyL''⟩, rfl⟩
  have hcoL'' : ∀ z : ↥L'', (z : ℚ̄) = algebraMap (↥L'') ℚ̄ z := fun z => rfl
  have hytpow : yt ^ p₀ = algebraMap (↥L') (↥L'') (x : ↥L') := by
    have h1 : ((yt ^ p₀ : ↥L'') : ℚ̄) = ((algebraMap (↥L') (↥L'') (x : ↥L') : ↥L'') : ℚ̄) := by
      rw [SubmonoidClass.coe_pow, hytcoe, hy, hcoL,
        IsScalarTower.algebraMap_apply (↥L') (↥L'') ℚ̄]
      rfl
    exact Subtype.coe_injective h1

  have hd_eq : Module.finrank (↥L') ↥L'' = (minpoly (↥L') y).natDegree :=
    IntermediateField.adjoin.finrank hyint
  have hd_le : Module.finrank (↥L') ↥L'' ≤ p₀ := by
    rw [hd_eq]
    have hdvd : minpoly (↥L') y ∣ Polynomial.X ^ p₀ - Polynomial.C (x : ↥L') :=
      minpoly.dvd _ _ haval
    calc (minpoly (↥L') y).natDegree
        ≤ (Polynomial.X ^ p₀ - Polynomial.C (x : ↥L')).natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd (Polynomial.monic_X_pow_sub_C _ hp₀.ne_zero).ne_zero
      _ = p₀ := Polynomial.natDegree_X_pow_sub_C

  have hvbot : v.asIdeal ≠ ⊥ := v.ne_bot
  have : v.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hvbot v.isPrime
  have : Module.Finite (𝓞 L') (𝓞 ↥L'') :=
    Module.Finite.of_restrictScalars_finite ℤ (𝓞 L') (𝓞 ↥L'')
  have : Algebra.IsIntegral (𝓞 L') (𝓞 ↥L'') := Algebra.IsIntegral.of_finite _ _

  obtain ⟨Q₁, -, hQ₁prime, hQ₁comap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 ↥L''))
      (by rw [Ideal.under_def, Ideal.comap_bot_of_injective _ ringOfIntegersMap_injective]; exact bot_le)
  have := hQ₁prime
  have hQ₁lies : Q₁.LiesOver v.asIdeal := ⟨hQ₁comap.symm⟩
  have hQ₁bot : Q₁ ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hvbot Q₁
  set w₁ : HeightOneSpectrum (𝓞 ↥L'') := ⟨Q₁, hQ₁prime, hQ₁bot⟩ with hw₁def

  set W : Finset (Ideal (𝓞 ↥L'')) := IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 ↥L'')
    with hWdef
  have hmemW : ∀ u : Ideal (𝓞 ↥L''), u ∈ W ↔ u.IsPrime ∧ u.LiesOver v.asIdeal := by
    intro u
    rw [hWdef, IsDedekindDomain.mem_primesOverFinset_iff hvbot]
    exact Iff.rfl
  have hw₁W : w₁.asIdeal ∈ W := (hmemW _).mpr ⟨hQ₁prime, hQ₁lies⟩
  have hinj : Function.Injective (algebraMap (𝓞 L') (𝓞 ↥L'')) := ringOfIntegersMap_injective

  have hlow : ∀ u ∈ W, p₀ ≤ Ideal.ramificationIdx' v.asIdeal u * u.inertiaDeg (𝓞 L') := by
    intro u huW
    obtain ⟨hup, hul⟩ := (hmemW u).mp huW
    have := hup
    have := hul
    have hubot : u ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hvbot u
    set wu : HeightOneSpectrum (𝓞 ↥L'') := ⟨u, hup, hubot⟩ with hwudef
    have hdvd_e : p₀ ∣ Ideal.ramificationIdx' v.asIdeal u := by
      rw [← multiplicity_map_eq_ramificationIdx hinj v wu]
      exact p0_dvd_multiplicity_map p₀ hp₀ x v hv yt hytpow wu hul.over.symm
    have he0 : Ideal.ramificationIdx' v.asIdeal u ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver u hvbot
    have hf0 : 0 < u.inertiaDeg (𝓞 L') := Ideal.inertiaDeg_pos u (𝓞 L')
    calc p₀ ≤ Ideal.ramificationIdx' v.asIdeal u := Nat.le_of_dvd (Nat.pos_of_ne_zero he0) hdvd_e
      _ ≤ Ideal.ramificationIdx' v.asIdeal u * u.inertiaDeg (𝓞 L') :=
          Nat.le_mul_of_pos_right _ hf0
  have hsum0 : ∑ u ∈ W, Ideal.ramificationIdx' v.asIdeal u * u.inertiaDeg (𝓞 L') =
      Module.finrank (↥L') ↥L'' :=
    by
    letI := Fintype.ofFinite (v.asIdeal.primesOver (𝓞 ↥L''))
    calc
      ∑ u ∈ W, Ideal.ramificationIdx' v.asIdeal u * u.inertiaDeg (𝓞 L') =
          ∑ u : v.asIdeal.primesOver (𝓞 ↥L''),
            u.1.ramificationIdx (𝓞 L') * u.1.inertiaDeg (𝓞 L') := by
        apply Finset.sum_bij
          (fun u hu => (⟨u, (hmemW u).mp hu⟩ : v.asIdeal.primesOver (𝓞 ↥L'')))
        · intro u hu
          exact Finset.mem_univ _
        · intro u hu z hz h
          exact congrArg Subtype.val h
        · intro u hu
          exact ⟨u.1, (hmemW u.1).mpr u.2, Subtype.eta u.1 u.2⟩
        · intro u hu
          obtain ⟨hup, hul⟩ := (hmemW u).mp hu
          have := hup
          have := hul
          rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal u hvbot]
      _ = Module.finrank (𝓞 L') (𝓞 ↥L'') :=
        Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 ↥L'')
      _ = Module.finrank (↥L') ↥L'' :=
        (IsFractionRing.finrank_eq (𝓞 L') (↥L') (𝓞 ↥L'') (↥L'')).symm

  have hd_ge : p₀ ≤ Module.finrank (↥L') ↥L'' := by
    rw [← hsum0]
    calc p₀ ≤ Ideal.ramificationIdx' v.asIdeal w₁.asIdeal * w₁.asIdeal.inertiaDeg (𝓞 L') :=
        hlow _ hw₁W
      _ ≤ _ := Finset.single_le_sum
          (f := fun u => Ideal.ramificationIdx' v.asIdeal u * u.inertiaDeg (𝓞 L'))
          (fun i _ => Nat.zero_le _) hw₁W
  have hd_p₀ : Module.finrank (↥L') ↥L'' = p₀ := le_antisymm hd_le hd_ge
  have hsum : ∑ u ∈ W, Ideal.ramificationIdx' v.asIdeal u * u.inertiaDeg (𝓞 L') = p₀ := by
    rw [hsum0, hd_p₀]
  obtain ⟨hWsingle, hef⟩ := finset_sum_squeeze hp₀.pos w₁.asIdeal hw₁W hsum hlow
  have huniq : ∀ u : Ideal (𝓞 ↥L''), u.IsPrime → u.LiesOver v.asIdeal → u = w₁.asIdeal := by
    intro u h1 h2
    have : u ∈ W := (hmemW u).mpr ⟨h1, h2⟩
    rw [hWsingle] at this
    exact Finset.mem_singleton.mp this

  have he_dvd : p₀ ∣ Ideal.ramificationIdx' v.asIdeal w₁.asIdeal := by
    rw [← multiplicity_map_eq_ramificationIdx hinj v w₁]
    exact p0_dvd_multiplicity_map p₀ hp₀ x v hv yt hytpow w₁ hQ₁lies.over.symm
  have he0 : Ideal.ramificationIdx' v.asIdeal w₁.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w₁.asIdeal hvbot
  have hf0 : 0 < w₁.asIdeal.inertiaDeg (𝓞 L') := Ideal.inertiaDeg_pos w₁.asIdeal (𝓞 L')
  have he_p₀ : Ideal.ramificationIdx' v.asIdeal w₁.asIdeal = p₀ := by
    have h1 : p₀ ≤ Ideal.ramificationIdx' v.asIdeal w₁.asIdeal :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero he0) he_dvd
    have h2 : Ideal.ramificationIdx' v.asIdeal w₁.asIdeal ≤ p₀ := by
      calc Ideal.ramificationIdx' v.asIdeal w₁.asIdeal
          ≤ Ideal.ramificationIdx' v.asIdeal w₁.asIdeal * w₁.asIdeal.inertiaDeg (𝓞 L') :=
            Nat.le_mul_of_pos_right _ hf0
        _ = p₀ := hef
    exact le_antisymm h2 h1
  have hf_1 : w₁.asIdeal.inertiaDeg (𝓞 L') = 1 := by
    have := hef
    rw [he_p₀] at this
    exact Nat.eq_of_mul_eq_mul_left hp₀.pos (by rw [mul_one]; exact this)

  obtain ⟨𝔓, -, h𝔓prime, h𝔓comap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral w₁.asIdeal (⊥ : Ideal (𝓞 ℚ̄))
      (by rw [Ideal.under_def, Ideal.comap_bot_of_injective _ ringOfIntegersMap_injective]; exact bot_le)
  have := h𝔓prime
  have h𝔓lies : 𝔓.LiesOver w₁.asIdeal := ⟨h𝔓comap.symm⟩

  have htower𝓞 : IsScalarTower (𝓞 L') (𝓞 ↥L'') (𝓞 ℚ̄) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    apply NumberField.RingOfIntegers.ext
    rw [coe_ringOfIntegersMap, coe_ringOfIntegersMap, coe_ringOfIntegersMap,
      IsScalarTower.algebraMap_apply (↥L') (↥L'') ℚ̄]
  have htrans : ∀ I : Ideal (𝓞 ℚ̄), (I.under (𝓞 ↥L'')).under (𝓞 L') = I.under (𝓞 L') := by
    intro I
    rw [Ideal.under, Ideal.under, Ideal.under, Ideal.comap_comap,
      ← IsScalarTower.algebraMap_eq (𝓞 L') (𝓞 ↥L'') (𝓞 ℚ̄)]
  have h𝔓L'' : 𝔓.under (𝓞 ↥L'') = w₁.asIdeal := h𝔓comap
  have h𝔓L' : 𝔓.under (𝓞 L') = v.asIdeal := by
    rw [← htrans 𝔓, h𝔓L'']
    exact hQ₁comap

  have hdeg2 : 1 < (minpoly (↥L') y).natDegree := by
    rw [← hd_eq, hd_p₀]
    exact hp₀.one_lt
  obtain ⟨y₁, hy₁root, hy₁ne⟩ := exists_second_root L' y hyint hdeg2
  obtain ⟨σ₀, hσ₀⟩ := exists_algEquiv_map_root L' y y₁ hy₁root

  have hσ₀𝔓prime : (σ₀ • 𝔓).IsPrime := by
    rw [Ideal.pointwise_smul_eq_comap]
    infer_instance
  have hσ₀under : (σ₀ • 𝔓).under (𝓞 L') = v.asIdeal := by
    rw [Ideal.under_smul]
    exact h𝔓L'
  have hσ₀L'' : (σ₀ • 𝔓).under (𝓞 ↥L'') = w₁.asIdeal := by
    refine huniq _ (Ideal.IsPrime.under (𝓞 ↥L'') (σ₀ • 𝔓)) ⟨?_⟩
    rw [htrans (σ₀ • 𝔓), hσ₀under]
  have hunder_eq : 𝔓.under (𝓞 ↥L'') = (σ₀ • 𝔓).under (𝓞 ↥L'') := by
    rw [h𝔓L'', hσ₀L'']
  obtain ⟨ρ, hρ⟩ := exists_gal_smul_of_under_eq (↥L'') 𝔓 (σ₀ • 𝔓) hunder_eq

  have hresb : ∀ (g : ℚ̄ ≃ₐ[↥L''] ℚ̄) (b : 𝓞 ℚ̄),
      (AlgEquiv.restrictScalars (↥L') g) • b = g • b := fun g b =>
    NumberField.RingOfIntegers.ext rfl
  have hresbinv : ∀ (g : ℚ̄ ≃ₐ[↥L''] ℚ̄) (b : 𝓞 ℚ̄),
      (AlgEquiv.restrictScalars (↥L') g)⁻¹ • b = g⁻¹ • b := fun g b =>
    NumberField.RingOfIntegers.ext rfl
  have hresI : ∀ (g : ℚ̄ ≃ₐ[↥L''] ℚ̄) (I : Ideal (𝓞 ℚ̄)),
      (AlgEquiv.restrictScalars (↥L') g) • I = g • I := fun g I =>
    smul_ideal_congr _ _ (hresbinv g) I

  set σ₁ : ℚ̄ ≃ₐ[↥L'] ℚ̄ := (AlgEquiv.restrictScalars (↥L') ρ)⁻¹ * σ₀ with hσ₁def
  have hσ₁stab : σ₁ • 𝔓 = 𝔓 := by
    rw [hσ₁def, mul_smul, hρ, ← hresI ρ 𝔓, inv_smul_smul]
  have hσ₁mem : ∀ z ∈ 𝔓, σ₁ • z ∈ 𝔓 := by
    intro z hz
    have : σ₁ • z ∈ σ₁ • 𝔓 := by
      rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
      show σ₁⁻¹ • σ₁ • z ∈ 𝔓
      rwa [inv_smul_smul]
    rwa [hσ₁stab] at this

  have hsurj : Function.Surjective
      (algebraMap ((𝓞 L') ⧸ v.asIdeal) ((𝓞 ↥L'') ⧸ w₁.asIdeal)) := by
    have : w₁.asIdeal.IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime w₁.ne_bot w₁.isPrime
    letI : Field ((𝓞 L') ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    have hf := hf_1
    rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w₁.asIdeal] at hf
    exact (Module.Free.bijective_algebraMap_of_finrank_eq_one hf).2
  have hw₁to𝔓 : ∀ z : 𝓞 ↥L'', z ∈ w₁.asIdeal → algebraMap (𝓞 ↥L'') (𝓞 ℚ̄) z ∈ 𝔓 := by
    intro z hz
    rw [← h𝔓L''] at hz
    exact Ideal.mem_comap.mp hz
  have hmaincong : ∀ c : 𝓞 ↥L'',
      σ₁ • algebraMap (𝓞 ↥L'') (𝓞 ℚ̄) c - algebraMap (𝓞 ↥L'') (𝓞 ℚ̄) c ∈ 𝔓 := by
    intro c
    obtain ⟨c'q, hc'⟩ := hsurj (Ideal.Quotient.mk w₁.asIdeal c)
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c'q
    have hc'' : Ideal.Quotient.mk w₁.asIdeal (algebraMap (𝓞 L') (𝓞 ↥L'') c') =
        Ideal.Quotient.mk w₁.asIdeal c := by
      rw [← hc']
      rfl
    have hw₁sub : c - algebraMap (𝓞 L') (𝓞 ↥L'') c' ∈ w₁.asIdeal :=
      Ideal.Quotient.eq.mp hc''.symm
    have hB : algebraMap (𝓞 ↥L'') (𝓞 ℚ̄) c - algebraMap (𝓞 L') (𝓞 ℚ̄) c' ∈ 𝔓 := by
      have := hw₁to𝔓 _ hw₁sub
      rwa [map_sub, ← IsScalarTower.algebraMap_apply (𝓞 L') (𝓞 ↥L'') (𝓞 ℚ̄)] at this
    have h1 : σ₁ • (algebraMap (𝓞 ↥L'') (𝓞 ℚ̄) c - algebraMap (𝓞 L') (𝓞 ℚ̄) c') ∈ 𝔓 :=
      hσ₁mem _ hB
    rw [smul_sub, galSmul_ringOfIntegersMap σ₁ c'] at h1
    have h2' : algebraMap (𝓞 L') (𝓞 ℚ̄) c' - algebraMap (𝓞 ↥L'') (𝓞 ℚ̄) c ∈ 𝔓 := by
      have := neg_mem hB
      rwa [neg_sub] at this
    have h2 := Ideal.add_mem 𝔓 h1 h2'
    rwa [sub_add_sub_cancel] at h2

  have hsmulmap : Ideal.map ((MulSemiringAction.toRingAut (ℚ̄ ≃ₐ[↥L'] ℚ̄) (𝓞 ℚ̄) σ₁) :
      𝓞 ℚ̄ ≃+* 𝓞 ℚ̄) 𝔓 = σ₁ • 𝔓 := by
    rw [Ideal.pointwise_smul_eq_comap, Ideal.comap_symm]
  have hmapeq : 𝔓 = Ideal.map ((MulSemiringAction.toRingAut (ℚ̄ ≃ₐ[↥L'] ℚ̄) (𝓞 ℚ̄) σ₁) :
      𝓞 ℚ̄ ≃+* 𝓞 ℚ̄) 𝔓 := by
    rw [hsmulmap, hσ₁stab]
  set φraw : (𝓞 ℚ̄ ⧸ 𝔓) ≃+* (𝓞 ℚ̄ ⧸ 𝔓) :=
    Ideal.quotientEquiv 𝔓 𝔓 ((MulSemiringAction.toRingAut (ℚ̄ ≃ₐ[↥L'] ℚ̄) (𝓞 ℚ̄) σ₁) :
      𝓞 ℚ̄ ≃+* 𝓞 ℚ̄) hmapeq with hφrawdef
  have hφraw_mk : ∀ z : 𝓞 ℚ̄, φraw (Ideal.Quotient.mk 𝔓 z) = Ideal.Quotient.mk 𝔓 (σ₁ • z) := by
    intro z
    rfl
  set φ₁ : (𝓞 ℚ̄ ⧸ 𝔓) ≃ₐ[(𝓞 ↥L'') ⧸ w₁.asIdeal] (𝓞 ℚ̄ ⧸ 𝔓) :=
    AlgEquiv.ofRingEquiv (f := φraw) (by
      intro cq
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective cq
      have halg : algebraMap ((𝓞 ↥L'') ⧸ w₁.asIdeal) (𝓞 ℚ̄ ⧸ 𝔓)
          (Ideal.Quotient.mk w₁.asIdeal c) =
          Ideal.Quotient.mk 𝔓 (algebraMap (𝓞 ↥L'') (𝓞 ℚ̄) c) := rfl
      rw [halg, hφraw_mk]
      exact Ideal.Quotient.eq.mpr (hmaincong c)) with hφ₁def
  obtain ⟨δ, hδ⟩ := stabilizerHom_surjective_gal (↥L'') w₁.asIdeal 𝔓 φ₁⁻¹

  set σ₂ : ℚ̄ ≃ₐ[↥L'] ℚ̄ :=
    (AlgEquiv.restrictScalars (↥L') (δ : ℚ̄ ≃ₐ[↥L''] ℚ̄)) * σ₁ with hσ₂def
  have hδstab : (δ : ℚ̄ ≃ₐ[↥L''] ℚ̄) • 𝔓 = 𝔓 := δ.2
  have hσ₂stab : σ₂ • 𝔓 = 𝔓 := by
    rw [hσ₂def, mul_smul, hσ₁stab, hresI, hδstab]
  have hσ₂mem : ∀ z ∈ 𝔓, σ₂ • z ∈ 𝔓 := by
    intro z hz
    have : σ₂ • z ∈ σ₂ • 𝔓 := by
      rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
      show σ₂⁻¹ • σ₂ • z ∈ 𝔓
      rwa [inv_smul_smul]
    rwa [hσ₂stab] at this
  have hσ₂meminv : ∀ z : 𝓞 ℚ̄, σ₂ • z ∈ 𝔓 → z ∈ 𝔓 := by
    intro z hz
    rw [← hσ₂stab, Ideal.pointwise_smul_eq_comap, Ideal.mem_comap] at hz
    rwa [show ((MulSemiringAction.toRingAut (ℚ̄ ≃ₐ[↥L'] ℚ̄) (𝓞 ℚ̄) σ₂).symm :
        𝓞 ℚ̄ ≃+* 𝓞 ℚ̄) (σ₂ • z) = z from by
      rw [RingEquiv.symm_apply_eq]
      rfl] at hz

  have hσ₂res : ∀ b : 𝓞 ℚ̄, σ₂ • b - b ∈ 𝔓 := by
    intro b
    rw [← Ideal.Quotient.eq]
    have h1 : σ₂ • b = (δ : ℚ̄ ≃ₐ[↥L''] ℚ̄) • (σ₁ • b) := by
      rw [hσ₂def, mul_smul, hresb]
    rw [h1, show Ideal.Quotient.mk 𝔓 ((δ : ℚ̄ ≃ₐ[↥L''] ℚ̄) • (σ₁ • b)) =
        Ideal.Quotient.stabilizerHom 𝔓 w₁.asIdeal (ℚ̄ ≃ₐ[↥L''] ℚ̄) δ
          (Ideal.Quotient.mk 𝔓 (σ₁ • b)) from
      (Ideal.Quotient.stabilizerHom_apply 𝔓 w₁.asIdeal (ℚ̄ ≃ₐ[↥L''] ℚ̄) δ (σ₁ • b)).symm,
      hδ, show Ideal.Quotient.mk 𝔓 (σ₁ • b) = φ₁ (Ideal.Quotient.mk 𝔓 b) from
        (hφraw_mk b).symm,
      show (φ₁⁻¹ : (𝓞 ℚ̄ ⧸ 𝔓) ≃ₐ[(𝓞 ↥L'') ⧸ w₁.asIdeal] (𝓞 ℚ̄ ⧸ 𝔓)) = φ₁.symm from rfl,
      AlgEquiv.symm_apply_apply]

  have hfixgal : ∀ (g : ℚ̄ ≃ₐ[↥L''] ℚ̄) (w : ℚ̄), w ∈ L'' → g w = w := by
    intro g w hw
    exact gal_fix_of_mem_range g ⟨⟨w, hw⟩, rfl⟩
  have hyrange : y ∈ L'' := hyL''
  have hσ₂fix : ∀ z : ↥L', σ₂ (z : ℚ̄) = z := by
    intro z
    have hzL'' : (z : ℚ̄) ∈ L'' := by
      rw [hcoL]
      exact L''.algebraMap_mem z
    have h0 : σ₀ (z : ℚ̄) = z := by
      rw [hcoL]
      exact σ₀.commutes z
    have h1 : σ₁ (z : ℚ̄) = z := by
      rw [hσ₁def, AlgEquiv.mul_apply, h0]
      exact hfixgal ρ⁻¹ _ hzL''
    rw [hσ₂def, AlgEquiv.mul_apply, h1]
    exact hfixgal (δ : ℚ̄ ≃ₐ[↥L''] ℚ̄) _ hzL''
  have hσ₂y : σ₂ y ≠ y := by
    intro hcontra
    have h1 : σ₂ y = (δ : ℚ̄ ≃ₐ[↥L''] ℚ̄) (((AlgEquiv.restrictScalars (↥L') ρ)⁻¹ * σ₀) y) := by
      rw [hσ₂def, AlgEquiv.mul_apply]
      rfl
    have h2 : ((AlgEquiv.restrictScalars (↥L') ρ)⁻¹ * σ₀) y = ρ⁻¹ y₁ := by
      rw [AlgEquiv.mul_apply, hσ₀]
      rfl
    rw [h1, h2] at hcontra

    have h3 : ρ⁻¹ y₁ = (δ : ℚ̄ ≃ₐ[↥L''] ℚ̄)⁻¹ y := by
      rw [← hcontra]
      show ρ⁻¹ y₁ = (δ : ℚ̄ ≃ₐ[↥L''] ℚ̄).symm ((δ : ℚ̄ ≃ₐ[↥L''] ℚ̄) (ρ⁻¹ y₁))
      rw [AlgEquiv.symm_apply_apply]
    have h4 : (δ : ℚ̄ ≃ₐ[↥L''] ℚ̄)⁻¹ y = y := hfixgal _ y hyrange
    rw [h4] at h3
    have h5 : y₁ = ρ y := by
      rw [show ρ⁻¹ y₁ = ρ.symm y₁ from rfl] at h3
      rw [← h3, AlgEquiv.apply_symm_apply]
    have h6 : ρ y = y := hfixgal ρ y hyrange
    exact hy₁ne (by rw [h5, h6])

  have hq𝔓 : (q : 𝓞 ℚ̄) ∈ 𝔓 := by
    have h1 : (q : 𝓞 L') ∈ 𝔓.under (𝓞 L') := by
      rw [h𝔓L']
      exact hqv
    have h2 := Ideal.mem_comap.mp h1
    rwa [map_natCast] at h2
  have hq0 : (q : 𝓞 ℚ̄) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have h𝔓bot : 𝔓 ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hq𝔓
    exact hq0 hq𝔓

  obtain ⟨P, hPmem⟩ : ∃ P : ValuationSubring ℚ̄,
      ∀ α : ℚ̄, α ∈ P ↔ ∃ a s : 𝓞 ℚ̄, s ∉ 𝔓 ∧ α = (a : ℚ̄) * (s : ℚ̄)⁻¹ :=
    ⟨placeAt 𝔓 h𝔓bot, fun α => mem_placeAt⟩
  have hcoe𝓞 : ∀ a : 𝓞 ℚ̄, (a : ℚ̄) = algebraMap (𝓞 ℚ̄) ℚ̄ a := fun a => rfl
  have hqQ0 : (q : ℚ̄) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero

  have hLies : P.LiesOverPrime q := by
    show (q : ℚ̄) ∈ P.nonunits
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro hmem
    obtain ⟨a, s, hs, heq⟩ := (hPmem _).mp hmem
    have hsne : (s : ℚ̄) ≠ 0 := coe_ne_zero_of_notMem hs
    have h2 : (s : ℚ̄) = (q : ℚ̄) * a := by
      calc (s : ℚ̄) = ((q : ℚ̄)⁻¹ * q) * s := by rw [inv_mul_cancel₀ hqQ0, one_mul]
      _ = ((a : ℚ̄) * (s : ℚ̄)⁻¹ * q) * s := by rw [← heq]
      _ = (q : ℚ̄) * a * ((s : ℚ̄)⁻¹ * s) := by ring
      _ = (q : ℚ̄) * a := by rw [inv_mul_cancel₀ hsne, mul_one]
    have h3 : s = (q : 𝓞 ℚ̄) * a := by
      apply NumberField.RingOfIntegers.coe_injective
      push_cast
      exact h2
    exact hs (h3 ▸ Ideal.mul_mem_right a _ hq𝔓)

  have hstabP : ∀ (g : ℚ̄ ≃ₐ[↥L'] ℚ̄), (∀ z ∈ 𝔓, g • z ∈ 𝔓) → (∀ z : 𝓞 ℚ̄, g • z ∈ 𝔓 → z ∈ 𝔓) →
      ∀ α ∈ P, g α ∈ P := by
    intro g hg hg' α hα
    obtain ⟨a, s, hs, rfl⟩ := (hPmem α).mp hα
    refine (hPmem _).mpr ⟨g • a, g • s, fun hmem => hs (hg' s hmem), ?_⟩
    rw [map_mul, map_inv₀, show g (a : ℚ̄) = ((g • a : 𝓞 ℚ̄) : ℚ̄) from (coe_galSmul g a).symm,
      show g (s : ℚ̄) = ((g • s : 𝓞 ℚ̄) : ℚ̄) from (coe_galSmul g s).symm]
  have hσ₂invmem : ∀ z ∈ 𝔓, σ₂⁻¹ • z ∈ 𝔓 := by
    intro z hz
    apply hσ₂meminv
    rwa [smul_inv_smul]
  have hσ₂invmem' : ∀ z : 𝓞 ℚ̄, σ₂⁻¹ • z ∈ 𝔓 → z ∈ 𝔓 := by
    intro z hz
    have := hσ₂mem _ hz
    rwa [smul_inv_smul] at this
  set σ : ℚ̄ ≃ₐ[ℚ] ℚ̄ := AlgEquiv.restrictScalars ℚ σ₂ with hσdef
  have hσapp : ∀ w : ℚ̄, σ w = σ₂ w := fun w => rfl
  have hσinvapp : ∀ w : ℚ̄, σ⁻¹ w = σ₂⁻¹ w := fun w => rfl
  have hdec : σ ∈ P.decompositionSubgroup ℚ := by
    show σ • P = P
    apply SetLike.ext
    intro α
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro hmem
      have h1 : σ₂ (σ⁻¹ • α) ∈ P := hstabP σ₂ hσ₂mem hσ₂meminv _ hmem
      rwa [show σ⁻¹ • α = σ₂⁻¹ α from by rw [AlgEquiv.smul_def]; exact hσinvapp α,
        show σ₂ (σ₂⁻¹ α) = α from by
          rw [show σ₂⁻¹ α = σ₂.symm α from rfl, AlgEquiv.apply_symm_apply]] at h1
    · intro hmem
      rw [AlgEquiv.smul_def, hσinvapp]
      exact hstabP σ₂⁻¹ hσ₂invmem hσ₂invmem' α hmem

  have hinertia : σ ∈ P.inertiaSubgroupIn ℚ := by
    rw [ValuationSubring.inertiaSubgroupIn]
    refine Subgroup.mem_map.mpr ⟨⟨σ, hdec⟩, ?_, rfl⟩
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro ξ
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective (R := ↥P) ξ
    show (⟨σ, hdec⟩ : P.decompositionSubgroup ℚ) • IsLocalRing.residue ↥P z =
      IsLocalRing.residue ↥P z
    rw [← IsLocalRing.ResidueField.residue_smul]
    apply Ideal.Quotient.eq.mpr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    obtain ⟨w'P, hw'P⟩ := hunit.exists_right_inv

    have hsmulcoe : (((⟨σ, hdec⟩ : P.decompositionSubgroup ℚ) • z : ↥P) : ℚ̄) = σ₂ (z : ℚ̄) :=
      rfl
    set d : ℚ̄ := σ₂ (z : ℚ̄) - (z : ℚ̄) with hddef
    have hdw' : d * (w'P : ℚ̄) = 1 := by
      have h0 := congrArg (fun t : ↥P => (t : ℚ̄)) hw'P
      push_cast at h0
      rwa [hsmulcoe, ← hddef] at h0
    have hd0 : d ≠ 0 := by
      intro h
      rw [h, zero_mul] at hdw'
      exact zero_ne_one hdw'
    have hw'inv : (w'P : ℚ̄) = d⁻¹ := eq_inv_of_mul_eq_one_right hdw'

    obtain ⟨a, s, hs, hzeq⟩ := (hPmem (z : ℚ̄)).mp (SetLike.coe_mem z)
    have hsne : (s : ℚ̄) ≠ 0 := coe_ne_zero_of_notMem hs
    have hσ₂snot : σ₂ • s ∉ 𝔓 := fun h => hs (hσ₂meminv s h)
    have hσ₂sne : ((σ₂ • s : 𝓞 ℚ̄) : ℚ̄) ≠ 0 := coe_ne_zero_of_notMem hσ₂snot

    set N : 𝓞 ℚ̄ := (σ₂ • a) * s - a * (σ₂ • s) with hNdef
    have hN𝔓 : N ∈ 𝔓 := by
      have hdecomp : N = (σ₂ • a - a) * s - a * (σ₂ • s - s) := by
        rw [hNdef]
        ring
      rw [hdecomp]
      exact Ideal.sub_mem _ (Ideal.mul_mem_right s _ (hσ₂res a))
        (Ideal.mul_mem_left _ a (hσ₂res s))
    set D : 𝓞 ℚ̄ := (σ₂ • s) * s with hDdef
    have hD𝔓 : D ∉ 𝔓 := by
      intro h
      rcases h𝔓prime.mem_or_mem h with h | h
      · exact hσ₂snot h
      · exact hs h

    have hd_frac : d = (N : ℚ̄) / (D : ℚ̄) := by
      have hσ₂z : σ₂ (z : ℚ̄) = ((σ₂ • a : 𝓞 ℚ̄) : ℚ̄) / ((σ₂ • s : 𝓞 ℚ̄) : ℚ̄) := by
        rw [hzeq, map_mul, map_inv₀, ← div_eq_mul_inv,
          show σ₂ (a : ℚ̄) = ((σ₂ • a : 𝓞 ℚ̄) : ℚ̄) from (coe_galSmul σ₂ a).symm,
          show σ₂ (s : ℚ̄) = ((σ₂ • s : 𝓞 ℚ̄) : ℚ̄) from (coe_galSmul σ₂ s).symm]
      rw [hddef, hσ₂z, hzeq, ← div_eq_mul_inv,
        div_sub_div _ _ hσ₂sne hsne]
      rw [hNdef, hDdef]
      push_cast
      ring_nf

    have hNne : (N : ℚ̄) ≠ 0 := by
      intro h
      rw [hd_frac, h, zero_div] at hd0
      exact hd0 rfl
    obtain ⟨c, t, ht, hw'eq⟩ := (hPmem (w'P : ℚ̄)).mp (SetLike.coe_mem w'P)
    have htne : (t : ℚ̄) ≠ 0 := coe_ne_zero_of_notMem ht
    have hdinv : (D : ℚ̄) / (N : ℚ̄) = (c : ℚ̄) / (t : ℚ̄) := by
      have h1 : d⁻¹ = (D : ℚ̄) / (N : ℚ̄) := by
        rw [hd_frac, inv_div]
      rw [← h1, ← hw'inv, hw'eq, div_eq_mul_inv]
    have hcross : D * t = N * c := by
      apply NumberField.RingOfIntegers.coe_injective
      push_cast
      have h4 := (div_eq_div_iff hNne htne).mp hdinv
      rw [mul_comm (c : ℚ̄) (N : ℚ̄)] at h4
      exact h4
    have hDt𝔓 : D * t ∈ 𝔓 := hcross ▸ Ideal.mul_mem_right c _ hN𝔓
    rcases h𝔓prime.mem_or_mem hDt𝔓 with h | h
    · exact hD𝔓 h
    · exact ht h

  exact ⟨P, hLies, pin_of_under_eq L' v 𝔓 h𝔓L' P hPmem, σ, hinertia, fun z => hσ₂fix z,
    fun h => hσ₂y ((hσapp y).symm.trans h)⟩

end WtTF
p2m_reactivate "P2MW.S_ValuationSubring_exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation.WtTF.RB P2MW.S_ValuationSubring_exists_forall_mem_asIdeal_iff_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation.WtTF"

theorem solution
    (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L']
    (p₀ : ℕ) (hp₀ : p₀.Prime) (x : (L' : Type)ˣ) (v : HeightOneSpectrum (𝓞 L'))
    (q : ℕ) (hq : q.Prime) (hqv : (q : 𝓞 L') ∈ v.asIdeal)
    (hv : ¬ ((p₀ : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x)))
    (y : AlgebraicClosure ℚ) (hy : y ^ p₀ = ((x : L') : AlgebraicClosure ℚ)) :
    ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q ∧
      (∀ z : 𝓞 L', z ∈ v.asIdeal ↔ P.valuation (algebraMap L' (AlgebraicClosure ℚ) z) < 1) ∧
      ∃ σ ∈ P.inertiaSubgroupIn ℚ, (∀ z : L', σ z = z) ∧ σ y ≠ y :=
  WtTF.exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd L' p₀ hp₀ x v q hq hqv hv y hy
