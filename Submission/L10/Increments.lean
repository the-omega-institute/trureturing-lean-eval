import Submission.L10.GOETail2

/-!
# Gate L-10 (`klartag_packing`), brief 6 — the increments

Klartag, arXiv:2504.05042, **Lemma 3.1** (p. 12-13) and **Corollary 3.2** (p. 13), in the discrete
form of hinge 1 (`research/lean-eval-next/klartag-hinge-2026-09-11.md` §2, item C2).

The continuous proof of Lemma 3.1 splits `A_t - a₀ Id` as `(W⁽¹⁾ + W⁽²⁾)/2` with
`W⁽¹⁾ = ∫ (π + π̃) dW`, `W⁽²⁾ = ∫ (π - π̃) dW`, and then invokes **Lévy's characterisation** of
Brownian motion to identify both as standard Brownian motions in `R^{n×n}_sym`, whence the GOE law
and Cor 3.2.

The discrete replacement removes Lévy's characterisation entirely.  `π_k ± π̃_k` is an
`F_k`-measurable **orthogonal involution** (`Submodule.reflection`), and the standard Gaussian is
invariant under every linear isometry (`ProbabilityTheory.stdGaussian_map`), so conditionally on
`F_k` the rotated increment is again standard Gaussian and *independent of `F_k`*
(`map_frozen_isometry`, `indepFun_frozen_isometry`).  Summing, the Maurey split is exact and the
GOE law is immediate.

Contents:
* Part 1 — rotational invariance, and the reflection `π - π̃`.
* Part 2 — the frozen (conditional) version: a random `F`-measurable isometry applied to an
  increment independent of `F` preserves the law *and* the independence.
* Part 3 — the projected step: the law of `π ξ`, and `E[f(π ξ) | F] = ∫ f(π x) dγ(x)`.
* Part 4 — the GOE law: the model of `R^{n×n}_sym` with the Frobenius inner product, and the exact
  hypothesis instance that `GateL10.goe_opNormTail` (`Submission/L10/GOETail2.lean`) consumes.
-/

namespace Submission.L10.Increments

open MeasureTheory ProbabilityTheory Matrix Finset
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

/-! ## Part 1. Rotational invariance of the standard Gaussian -/

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Rotational invariance.**  The standard Gaussian on a finite-dimensional real inner product
space is invariant under every linear isometry equivalence.  This is the one-line replacement for
the use of Lévy's characterisation in Klartag's Lemma 3.1. -/
theorem map_stdGaussian_isometry (U : E ≃ₗᵢ[ℝ] E) : (stdGaussian E).map U = stdGaussian E :=
  stdGaussian_map U

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `Submodule.reflection K` *is* the operator `π - π̃` of hinge 1 §2, with `π` the orthogonal
projection onto `K` and `π̃ = Id - π`. -/
theorem reflection_eq_proj_sub_proj (K : Submodule ℝ E) [K.HasOrthogonalProjection] (x : E) :
    K.reflection x = K.starProjection x - (x - K.starProjection x) := by
  rw [Submodule.reflection_apply, two_smul]; abel

/-- The instance of `map_stdGaussian_isometry` the chain uses: `π ± π̃` is an orthogonal
involution, so it preserves the standard Gaussian. -/
theorem map_stdGaussian_reflection (K : Submodule ℝ E) [K.HasOrthogonalProjection] :
    (stdGaussian E).map K.reflection = stdGaussian E :=
  stdGaussian_map _

end Rotation

/-! ## Part 2. The frozen (conditional) version

The sub-σ-algebra `F` of the paper is represented by a random variable `Z : Ω → α` that generates
it; `U` is an `F`-measurable isometry, i.e. a measurable function of `Z`.  This is the form the
chain's induction consumes: at step `k`, `Z` is the configuration of contact points (which
determines `π_k`), and `ξ` is the fresh increment. -/

section Frozen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {α : Type*} [MeasurableSpace α]

/-- **The frozen rotation, at the level of joint laws.**  Applying an isometry that depends
measurably on the first coordinate leaves a product measure with standard Gaussian second factor
unchanged.  Conditionally on the first coordinate this says exactly that `U_a ξ` is again standard
Gaussian, uniformly in `a`. -/
theorem map_prod_isometry (μ : Measure α) [SFinite μ] (U : α → (E ≃ₗᵢ[ℝ] E))
    (hU : Measurable fun q : α × E => U q.1 q.2) :
    (μ.prod (stdGaussian E)).map (fun q => (q.1, U q.1 q.2)) = μ.prod (stdGaussian E) := by
  have hmeas : Measurable fun q : α × E => (q.1, U q.1 q.2) := measurable_fst.prodMk hU
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hmeas hs, Measure.prod_apply (hmeas hs), Measure.prod_apply hs]
  refine lintegral_congr fun a => ?_
  have hpre : (Prod.mk a ⁻¹' ((fun q : α × E => (q.1, U q.1 q.2)) ⁻¹' s))
      = (U a) ⁻¹' (Prod.mk a ⁻¹' s) := rfl
  rw [hpre, ← Measure.map_apply (U a).continuous.measurable (measurable_prodMk_left hs),
    map_stdGaussian_isometry]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The random-variable form of `map_prod_isometry`: the *pair* `(Z, U_Z ξ)` has the same law as
`(Z, ξ)` whenever `ξ` is independent of `Z` and standard Gaussian. -/
theorem map_prod_eq_of_indepFun {Z : Ω → α} {ξ : Ω → E} (hZ : Measurable Z) (hξ : Measurable ξ)
    (hindep : IndepFun Z ξ P) (hlaw : P.map ξ = stdGaussian E)
    (U : α → (E ≃ₗᵢ[ℝ] E)) (hU : Measurable fun q : α × E => U q.1 q.2) :
    P.map (fun ω => (Z ω, U (Z ω) (ξ ω))) = P.map (fun ω => (Z ω, ξ ω)) := by
  have hpair : P.map (fun ω => (Z ω, ξ ω)) = (P.map Z).prod (stdGaussian E) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hξ.aemeasurable).1 hindep, hlaw]
  have hcomp : (fun ω => (Z ω, U (Z ω) (ξ ω)))
      = (fun q : α × E => (q.1, U q.1 q.2)) ∘ (fun ω => (Z ω, ξ ω)) := rfl
  rw [hcomp, ← Measure.map_map (measurable_fst.prodMk hU) (hZ.prodMk hξ), hpair,
    map_prod_isometry _ U hU]

/-- **The discrete replacement for Lévy's characterisation.**  If `ξ` is standard Gaussian and
independent of `Z`, and `U` is a measurable family of isometries, then `U_Z ξ` is again standard
Gaussian. -/
theorem map_frozen_isometry {Z : Ω → α} {ξ : Ω → E} (hZ : Measurable Z) (hξ : Measurable ξ)
    (hindep : IndepFun Z ξ P) (hlaw : P.map ξ = stdGaussian E)
    (U : α → (E ≃ₗᵢ[ℝ] E)) (hU : Measurable fun q : α × E => U q.1 q.2) :
    P.map (fun ω => U (Z ω) (ξ ω)) = stdGaussian E := by
  have hUZ : Measurable fun ω => U (Z ω) (ξ ω) := hU.comp (hZ.prodMk hξ)
  have h := map_prod_eq_of_indepFun hZ hξ hindep hlaw U hU
  have e1 : P.map (fun ω => U (Z ω) (ξ ω))
      = (P.map (fun ω => (Z ω, U (Z ω) (ξ ω)))).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hZ.prodMk hUZ)]; rfl
  have e2 : P.map ξ = (P.map (fun ω => (Z ω, ξ ω))).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hZ.prodMk hξ)]; rfl
  rw [e1, h, ← e2, hlaw]

/-- …and it is still independent of `Z`, i.e. of the σ-algebra `F`. -/
theorem indepFun_frozen_isometry {Z : Ω → α} {ξ : Ω → E} (hZ : Measurable Z) (hξ : Measurable ξ)
    (hindep : IndepFun Z ξ P) (hlaw : P.map ξ = stdGaussian E)
    (U : α → (E ≃ₗᵢ[ℝ] E)) (hU : Measurable fun q : α × E => U q.1 q.2) :
    IndepFun Z (fun ω => U (Z ω) (ξ ω)) P := by
  have hUZ : Measurable fun ω => U (Z ω) (ξ ω) := hU.comp (hZ.prodMk hξ)
  rw [indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hUZ.aemeasurable]
  rw [map_prod_eq_of_indepFun hZ hξ hindep hlaw U hU,
    (indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hξ.aemeasurable).1 hindep, hlaw,
    map_frozen_isometry hZ hξ hindep hlaw U hU]

omit [FiniteDimensional ℝ E] in
/-- The joint measurability hypothesis is automatic when the configuration space is countable,
which is the chain's case: `π_k` is determined by the finite set of contact points. -/
theorem measurable_uncurry_of_countable [Countable α] [MeasurableSingletonClass α]
    (U : α → (E ≃ₗᵢ[ℝ] E)) : Measurable fun q : α × E => U q.1 q.2 :=
  measurable_from_prod_countable_right fun a => (U a).continuous.measurable

end Frozen

/-! ## Part 3. The projected step -/

section Projected

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [mE : MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The characteristic function of a pushforward, when the map has an explicit "adjoint".  Stated
without `ContinuousLinearMap.adjoint` so that no `CompleteSpace` hypothesis is needed and the
formula can be used for maps into a different space. -/
theorem charFun_map_of_inner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [OpensMeasurableSpace F] (μ : Measure E) (L : E → F) (hL : Measurable L)
    (a : F → E)
    (h : ∀ x t, ⟪L x, t⟫ = ⟪x, a t⟫) (t : F) :
    charFun (μ.map L) t = charFun μ (a t) := by
  have hcont : Continuous fun y : F => Complex.exp ((⟪y, t⟫ : ℝ) * Complex.I) := by
    refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
    exact Complex.continuous_ofReal.comp
      (continuous_inner.comp (continuous_id.prodMk continuous_const))
  rw [charFun_apply, charFun_apply,
    integral_map hL.aemeasurable hcont.aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [h x t])

/-- **The projected step.**  `π ξ` is the centred Gaussian with covariance operator `π`: its
characteristic function is `exp (-‖π t‖² / 2)`.  This is the law of the standard Gaussian of `E`
restricted to `range π`; it is what "conditionally on `F_k`, `π_k ξ_k` is `N(0, h · π_k)`" means
(Klartag p. 12, eq. 38). -/
theorem charFun_map_starProjection (K : Submodule ℝ E) [K.HasOrthogonalProjection] (t : E) :
    charFun ((stdGaussian E).map K.starProjection) t =
      Complex.exp (-‖K.starProjection t‖ ^ 2 / 2) := by
  rw [charFun_map_of_inner _ _ K.starProjection.continuous.measurable K.starProjection
    (fun x t => K.starProjection_isSymmetric x t), charFun_stdGaussian]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {α : Type*} [mα : MeasurableSpace α]

/-- **The projected step splits.**  `π ξ` and `π̃ ξ = (Id - π) ξ` are independent.  Klartag gets
this for free from the independence of the Brownian increments in orthogonal directions; here it is
the factorisation of the characteristic function across the orthogonal decomposition
`‖π t₁ + π̃ t₂‖² = ‖π t₁‖² + ‖π̃ t₂‖²`. -/
theorem indepFun_starProjection (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {ξ : Ω → E} (hξ : Measurable ξ) (hlaw : P.map ξ = stdGaussian E) :
    IndepFun (fun ω => K.starProjection (ξ ω)) (fun ω => Kᗮ.starProjection (ξ ω)) P := by
  have hm1 : Measurable fun ω => K.starProjection (ξ ω) :=
    K.starProjection.continuous.measurable.comp hξ
  have hm2 : Measurable fun ω => Kᗮ.starProjection (ξ ω) :=
    Kᗮ.starProjection.continuous.measurable.comp hξ
  have hmap1 : P.map (fun ω => K.starProjection (ξ ω)) = (stdGaussian E).map K.starProjection := by
    rw [← hlaw, Measure.map_map K.starProjection.continuous.measurable hξ]; rfl
  have hmap2 : P.map (fun ω => Kᗮ.starProjection (ξ ω))
      = (stdGaussian E).map Kᗮ.starProjection := by
    rw [← hlaw, Measure.map_map Kᗮ.starProjection.continuous.measurable hξ]; rfl
  rw [indepFun_iff_charFun_prod hm1.aemeasurable hm2.aemeasurable]
  intro t
  set Ψ : E → WithLp 2 (E × E) :=
    fun x => WithLp.toLp 2 (K.starProjection x, Kᗮ.starProjection x) with hΨ
  have hΨmeas : Measurable Ψ := by
    refine (WithLp.measurable_toLp 2 (E × E)).comp ?_
    exact (K.starProjection.continuous.measurable).prodMk Kᗮ.starProjection.continuous.measurable
  have hjoint : P.map (fun ω => WithLp.toLp 2
      ((fun ω => K.starProjection (ξ ω)) ω, (fun ω => Kᗮ.starProjection (ξ ω)) ω))
      = (stdGaussian E).map Ψ := by
    rw [← hlaw, Measure.map_map hΨmeas hξ]; rfl
  have hadj : ∀ (x : E) (u : WithLp 2 (E × E)),
      ⟪Ψ x, u⟫ = ⟪x, K.starProjection (WithLp.ofLp u).1
        + Kᗮ.starProjection (WithLp.ofLp u).2⟫ := by
    intro x u
    rw [WithLp.prod_inner_apply]
    simp only [hΨ, WithLp.ofLp_toLp, inner_add_right]
    have e1 : ⟪K.starProjection x, (WithLp.ofLp u).1⟫
        = ⟪x, K.starProjection (WithLp.ofLp u).1⟫ := K.starProjection_isSymmetric x _
    have e2 : ⟪Kᗮ.starProjection x, (WithLp.ofLp u).2⟫
        = ⟪x, Kᗮ.starProjection (WithLp.ofLp u).2⟫ := Kᗮ.starProjection_isSymmetric x _
    rw [e1, e2]
  rw [hjoint, charFun_map_of_inner _ _ hΨmeas _ hadj t, charFun_stdGaussian,
    hmap1, hmap2, charFun_map_starProjection, charFun_map_starProjection, ← Complex.exp_add]
  congr 1
  have horth : ⟪K.starProjection (WithLp.ofLp t).1, Kᗮ.starProjection (WithLp.ofLp t).2⟫ = 0 := by
    exact Submodule.inner_right_of_mem_orthogonal (K.starProjection_apply_mem _)
      (Kᗮ.starProjection_apply_mem _)
  have hpyth : ‖K.starProjection (WithLp.ofLp t).1 + Kᗮ.starProjection (WithLp.ofLp t).2‖ ^ 2
      = ‖K.starProjection (WithLp.ofLp t).1‖ ^ 2
        + ‖Kᗮ.starProjection (WithLp.ofLp t).2‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    have horth2 : ⟪Kᗮ.starProjection (WithLp.ofLp t).2, K.starProjection (WithLp.ofLp t).1⟫
        = 0 := by rw [real_inner_comm]; exact horth
    simp only [inner_add_add_self]
    rw [horth, horth2]
    ring
  have hc : ((‖K.starProjection (WithLp.ofLp t).1
        + Kᗮ.starProjection (WithLp.ofLp t).2‖ : ℝ) : ℂ) ^ 2
      = ((‖K.starProjection (WithLp.ofLp t).1‖ : ℝ) : ℂ) ^ 2
        + ((‖Kᗮ.starProjection (WithLp.ofLp t).2‖ : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      hpyth]
  rw [hc]
  ring

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **The conditional law of the projected step**, in the form the brief asks for.  The
σ-algebra `F` is the one generated by a random variable `Z`; if `ξ` is independent of `Z` then for
every bounded measurable `f`, `E[f (π ξ) | F] = ∫ f (π x) dγ(x)` almost surely, where `γ` is the
law of `ξ`.  Here `π` is deterministic; for an `F`-measurable *random* `π` the corresponding
statement at the level of laws is `map_frozen_isometry`. -/
theorem condExp_comp_of_indepFun {Z : Ω → α} (hZ : Measurable Z) {ξ : Ω → E} (hξ : Measurable ξ)
    (hind : IndepFun ξ Z P) {f : E → ℝ} (hf : Measurable f) {π : E → E} (hπ : Measurable π) :
    P[fun ω => f (π (ξ ω)) | MeasurableSpace.comap Z mα] =ᵐ[P]
      fun _ => ∫ x, f (π x) ∂(P.map ξ) := by
  have hmZ : MeasurableSpace.comap Z mα ≤ ‹MeasurableSpace Ω› := hZ.comap_le
  have hξ' : Measurable[MeasurableSpace.comap ξ mE] ξ := comap_measurable ξ
  have hmeas : StronglyMeasurable[MeasurableSpace.comap ξ mE]
      (fun ω => f (π (ξ ω))) := Measurable.stronglyMeasurable ((hf.comp hπ).comp hξ')
  have hsf : SigmaFinite (P.trim hmZ) := by
    have : IsFiniteMeasure (P.trim hmZ) := isFiniteMeasure_trim hmZ
    infer_instance
  have h := condExp_indep_eq hξ.comap_le hmZ hmeas hind
  refine h.trans (Filter.Eventually.of_forall fun ω => ?_)
  show ∫ x, f (π (ξ x)) ∂P = ∫ x, f (π x) ∂(P.map ξ)
  exact (integral_map (φ := ξ) (f := fun x => f (π x)) hξ.aemeasurable
    (hf.comp hπ).aestronglyMeasurable).symm

end Projected

/-! ## Part 4. The GOE law of the symmetrised increment

Klartag's Corollary 3.2 reads the increment `W_t` of the driving Dyson Brownian motion as
`√(tn/2) · Γ` with `Γ` a GOE matrix: `Γ` symmetric, `(Γ_ij)_{i ≤ j}` independent centred Gaussians
with `E Γ_ij² = (1 + δ_ij)/n` (p. 13).

`R^{n×n}_sym` with the Frobenius inner product is modelled here by
`EuclideanSpace ℝ (UT n)`, `UT n` the upper triangle, through the linear map `symMat`, which is an
isometry onto the symmetric matrices: `∑ i j, (symMat x) i j * (symMat y) i j = ⟪x, y⟫`
(`sum_symMat_mul_eq_inner`).  A standard Gaussian on that space therefore has diagonal entries of
variance `1` and off-diagonal entries of variance `1/2`, i.e. `E G_ij² = (1 + δ_ij)/2`, which is
the GOE at `√(2/n)` scaling.

`GateL10.gaussian_opNormTail` (`Submission/L10/GOETail2.lean`) consumes a matrix of the form
`B + Bᵀ` with the entries of `B` independent over the **full** product `Fin n × Fin n`.  A
symmetric Gaussian matrix is *not* of that form on its own probability space (its entries above
and below the diagonal are equal, hence not independent), so the two are matched **in law**: the
auxiliary space `Aux n` below carries such a `B`, and `map_coordVec_eq_map_auxV` identifies the two
laws.  That is the whole content of Lemma 3.1 once Lévy's characterisation has been removed. -/

section GOE

variable {n : ℕ}

/-- The upper triangle, including the diagonal: the index set of the coordinates of a symmetric
matrix. -/
abbrev UT (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}

/-- The sorted pair `(min i j, max i j)`. -/
def up (i j : Fin n) : UT n := ⟨(min i j, max i j), min_le_max⟩

theorem up_comm (i j : Fin n) : up i j = up j i := by simp [up, min_comm, max_comm]

theorem up_of_le {i j : Fin n} (h : i ≤ j) : up i j = ⟨(i, j), h⟩ := by
  simp [up, min_eq_left h, max_eq_right h]

@[simp] theorem up_coe (p : UT n) : up p.1.1 p.1.2 = p := by rw [up_of_le p.2]

theorem up_eq_iff {a b c d : Fin n} (hab : a ≤ b) (hcd : c ≤ d) (h : up a b = up c d) :
    a = c ∧ b = d := by
  rw [up_of_le hab, up_of_le hcd] at h
  have h' := congrArg Subtype.val h
  simp only at h'
  exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

/-- The coordinate weight: `1` on the diagonal, `1/√2` off it.  These are the coefficients that
make `symMat` a Frobenius isometry. -/
def cc (p : UT n) : ℝ := if p.1.1 = p.1.2 then 1 else (Real.sqrt 2)⁻¹

theorem cc_diag {p : UT n} (h : p.1.1 = p.1.2) : cc p = 1 := by simp [cc, h]

theorem cc_offdiag {p : UT n} (h : p.1.1 ≠ p.1.2) : cc p * cc p = 1 / 2 := by
  simp only [cc, ite_eq_right h]
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem cc_sq (p : UT n) : cc p * cc p = if p.1.1 = p.1.2 then 1 else 1 / 2 := by
  by_cases h : p.1.1 = p.1.2
  · rw [ite_eq_left h, cc_diag h]; norm_num
  · rw [ite_eq_right h]; exact cc_offdiag h

/-- The symmetric matrix with the given Frobenius coordinates. -/
def symMat (x : EuclideanSpace ℝ (UT n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => cc (up i j) * x (up i j)

theorem symMat_apply (x : EuclideanSpace ℝ (UT n)) (i j : Fin n) :
    symMat x i j = cc (up i j) * x (up i j) := rfl

theorem symMat_isSymm (x : EuclideanSpace ℝ (UT n)) : (symMat x).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rw [symMat_apply, symMat_apply, up_comm]

theorem symMat_swap (x : EuclideanSpace ℝ (UT n)) (i j : Fin n) :
    symMat x j i = symMat x i j := by rw [symMat_apply, symMat_apply, up_comm]

theorem symMat_apply_ut (x : EuclideanSpace ℝ (UT n)) (p : UT n) :
    symMat x p.1.1 p.1.2 = cc p * x p := by rw [symMat_apply, up_coe]

/-- The fibre of the sorting map over `p` is the (possibly degenerate) pair `{(a,b), (b,a)}`. -/
theorem fiber_up (p : UT n) :
    (Finset.univ.filter fun q : Fin n × Fin n => up q.1 q.2 = p)
      = {(p.1.1, p.1.2), (p.1.2, p.1.1)} := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro h
    rcases le_total q.1 q.2 with hq | hq
    · left
      rw [up_of_le hq] at h
      have h' := congrArg Subtype.val h
      simp only at h'
      exact Prod.ext (congrArg Prod.fst h') (congrArg Prod.snd h')
    · right
      rw [up_comm, up_of_le hq] at h
      have h' := congrArg Subtype.val h
      simp only at h'
      exact Prod.ext (congrArg Prod.snd h') (congrArg Prod.fst h')
  · rintro (rfl | rfl)
    · exact up_coe p
    · rw [up_comm]; exact up_coe p

/-- **`symMat` is a Frobenius isometry.**  This is what justifies modelling `R^{n×n}_sym` by
`EuclideanSpace ℝ (UT n)`: the Euclidean inner product of the coordinates is the Frobenius inner
product `∑_{i,j} A_ij B_ij` of the matrices. -/
theorem sum_symMat_mul (x y : EuclideanSpace ℝ (UT n)) :
    ∑ q : Fin n × Fin n, symMat x q.1 q.2 * symMat y q.1 q.2 = ∑ p : UT n, x p * y p := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun q : Fin n × Fin n => up q.1 q.2) (fun q _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [fiber_up p]
  rcases eq_or_ne p.1.1 p.1.2 with hd | hd
  · have h1 : ((p.1.2, p.1.1) : Fin n × Fin n) = (p.1.1, p.1.2) := by rw [hd]
    rw [h1, Finset.pair_eq_singleton, Finset.sum_singleton, symMat_apply_ut, symMat_apply_ut,
      cc_diag hd]
    ring
  · have h2 : ((p.1.1, p.1.2) : Fin n × Fin n) ≠ (p.1.2, p.1.1) := fun h => hd (congrArg Prod.fst h)
    rw [Finset.sum_pair h2, symMat_swap x p.1.1 p.1.2, symMat_swap y p.1.1 p.1.2,
      symMat_apply_ut, symMat_apply_ut]
    have hcc := cc_offdiag hd
    linear_combination (2 * x.ofLp p * y.ofLp p) * hcc

theorem sum_symMat_mul_eq_inner (x y : EuclideanSpace ℝ (UT n)) :
    ∑ i, ∑ j, symMat x i j * symMat y i j = ⟪x, y⟫ := by
  have h := sum_symMat_mul x y
  rw [Fintype.sum_prod_type] at h
  rw [h]
  simp [PiLp.inner_apply, mul_comm]

/-! ### The matrix built from upper-triangular data, and the operator norm as a random variable -/

/-- The symmetric matrix with prescribed upper-triangular entries. -/
def mkMat (u : UT n → ℝ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => u (up i j)

/-- `mkMat` followed by `Matrix.toEuclideanCLM`, bundled as a linear map so that its continuity is
`LinearMap.continuous_of_finiteDimensional`. -/
def mkCLM (n : ℕ) :
    (UT n → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) where
  toFun u := Matrix.toEuclideanCLM (𝕜 := ℝ) (mkMat u)
  map_add' u v := by
    have h : mkMat (u + v) = mkMat u + mkMat v := by ext i j; simp [mkMat]
    rw [h, map_add]
  map_smul' c u := by
    have h : mkMat (c • u) = c • mkMat u := by ext i j; simp [mkMat]
    rw [h, map_smul]; rfl

theorem measurable_opNorm_mkMat :
    Measurable fun u : UT n → ℝ => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (mkMat u)‖ :=
  ((LinearMap.continuous_of_finiteDimensional (mkCLM n)).norm).measurable

/-- The Frobenius coordinates of the scaled symmetric Gaussian matrix. -/
def coordVec (r : ℝ) (x : EuclideanSpace ℝ (UT n)) : UT n → ℝ := fun p => r * cc p * x p

theorem measurable_coordVec (r : ℝ) : Measurable (coordVec (n := n) r) :=
  Measurable.of_eval fun p =>
    ((measurable_pi_apply p).comp (WithLp.measurable_ofLp _ _)).const_mul _

theorem smul_symMat_eq_mkMat (r : ℝ) (x : EuclideanSpace ℝ (UT n)) :
    r • symMat x = mkMat (coordVec r x) := by
  ext i j
  simp only [Matrix.smul_apply, symMat_apply, mkMat, Matrix.of_apply, coordVec, smul_eq_mul]
  ring

/-! ### The auxiliary i.i.d. model -/

/-- The auxiliary probability space carrying a matrix with i.i.d. entries: a product indexed by the
upper triangle and then by the two independent slots `B a b` and `B b a`. -/
abbrev Aux (n : ℕ) := UT n → Fin 2 → ℝ

def auxMeasure (n : ℕ) (v : ℝ≥0) : Measure (Aux n) :=
  Measure.pi fun _ : UT n => Measure.pi fun _ : Fin 2 => gaussianReal 0 v

instance (n : ℕ) (v : ℝ≥0) : IsProbabilityMeasure (auxMeasure n v) := by
  unfold auxMeasure; infer_instance

/-- The matrix with i.i.d. entries. -/
def auxB (ω : Aux n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ω (up i j) (if i ≤ j then 0 else 1)

/-- The index map `(i,j) ↦ (sorted pair, slot)`; it is injective, which is why the entries of
`auxB` are independent over the full product. -/
def eIdx (q : Fin n × Fin n) : UT n × Fin 2 := (up q.1 q.2, if q.1 ≤ q.2 then 0 else 1)

theorem eIdx_injective : Function.Injective (eIdx (n := n)) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  simp only [eIdx, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  by_cases hij : i ≤ j <;> by_cases hkl : k ≤ l
  · obtain ⟨e1, e2⟩ := up_eq_iff hij hkl h1
    simp [e1, e2]
  · simp [hij, hkl] at h2
  · simp [hij, hkl] at h2
  · rw [up_comm i j, up_comm k l] at h1
    obtain ⟨e1, e2⟩ := up_eq_iff (le_of_not_ge hij) (le_of_not_ge hkl) h1
    simp [e1, e2]

theorem aux_meas (p : UT n) (k : Fin 2) : Measurable fun ω : Aux n => ω p k :=
  (measurable_pi_apply k).comp (measurable_pi_apply p)

theorem aux_eval (v : ℝ≥0) (p : UT n) :
    (auxMeasure n v).map (fun ω : Aux n => ω p) = Measure.pi fun _ : Fin 2 => gaussianReal 0 v :=
  (measurePreserving_eval _ p).map_eq

theorem aux_eval2 (v : ℝ≥0) (p : UT n) (k : Fin 2) :
    (auxMeasure n v).map (fun ω : Aux n => ω p k) = gaussianReal 0 v := by
  have h : (fun ω : Aux n => ω p k) = (fun z : Fin 2 → ℝ => z k) ∘ (fun ω : Aux n => ω p) := rfl
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop), aux_eval,
    (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 v) k).map_eq]

theorem aux_inner_indep (v : ℝ≥0) (p : UT n) :
    iIndepFun (fun (k : Fin 2) (ω : Aux n) => ω p k) (auxMeasure n v) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun k => (aux_meas p k).aemeasurable)]
  rw [show (fun (ω : Aux n) (k : Fin 2) => ω p k) = (fun ω : Aux n => ω p) from rfl, aux_eval]
  congr 1
  funext k
  rw [aux_eval2]

theorem aux_coord_indep (v : ℝ≥0) :
    iIndepFun (fun (q : UT n × Fin 2) (ω : Aux n) => ω q.1 q.2) (auxMeasure n v) := by
  refine iIndepFun_uncurry' (fun i j => aux_meas i j) ?_ (aux_inner_indep v)
  exact iIndepFun_pi (X := fun _ : UT n => (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)))
    (fun _ => aemeasurable_id)

/-- **The first hypothesis `GateL10.gaussian_opNormTail` consumes**: the entries of `auxB` are
independent over the full product `Fin n × Fin n`. -/
theorem auxB_indep (v : ℝ≥0) :
    iIndepFun (fun (q : Fin n × Fin n) (ω : Aux n) => auxB ω q.1 q.2) (auxMeasure n v) :=
  (aux_coord_indep (n := n) v).precomp (eIdx_injective (n := n))

/-- **The second hypothesis `GateL10.gaussian_opNormTail` consumes**: every entry of `auxB` is
`N(0, v)`. -/
theorem auxB_law (v : ℝ≥0) (i j : Fin n) :
    (auxMeasure n v).map (fun ω : Aux n => auxB ω i j) = gaussianReal 0 v :=
  aux_eval2 v _ _

/-! ### Matching the two laws -/

/-- The block map producing the symmetrised entry from the two independent slots. -/
def phi (p : UT n) (z : Fin 2 → ℝ) : ℝ := if p.1.1 = p.1.2 then 2 * z 0 else z 0 + z 1

theorem measurable_phi (p : UT n) : Measurable (phi p) := by
  unfold phi; split
  · exact (measurable_pi_apply 0).const_mul 2
  · exact (measurable_pi_apply 0).add (measurable_pi_apply 1)

theorem phi_diag {p : UT n} (h : p.1.1 = p.1.2) : phi p = fun z : Fin 2 → ℝ => 2 * z 0 := by
  funext z; simp [phi, h]

theorem phi_offdiag {p : UT n} (h : p.1.1 ≠ p.1.2) :
    phi p = fun z : Fin 2 → ℝ => z 0 + z 1 := by
  funext z; simp [phi, h]

theorem auxV_eq (ω : Aux n) (p : UT n) :
    auxB ω p.1.1 p.1.2 + auxB ω p.1.2 p.1.1 = phi p (ω p) := by
  have h1 : auxB ω p.1.1 p.1.2 = ω p 0 := by
    simp only [auxB, Matrix.of_apply, up_coe, ite_eq_left p.2]
  have h2 : auxB ω p.1.2 p.1.1 = ω p (if p.1.2 ≤ p.1.1 then 0 else 1) := by
    simp only [auxB, Matrix.of_apply, up_comm p.1.2 p.1.1, up_coe]
  rw [h1, h2]
  unfold phi
  by_cases hd : p.1.1 = p.1.2
  · rw [ite_eq_left hd, ite_eq_left (le_of_eq hd.symm)]; ring
  · rw [ite_eq_right hd, ite_eq_right (fun h => hd (le_antisymm p.2 h))]

theorem auxB_add_transpose (ω : Aux n) :
    auxB ω + (auxB ω)ᵀ = mkMat (fun p => phi p (ω p)) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.transpose_apply, mkMat, Matrix.of_apply]
  rw [← auxV_eq ω (up i j)]
  rcases le_total i j with h | h
  · rw [up_of_le h]
  · rw [up_comm, up_of_le h]; ring

/-- `v = r²/4`: the entry variance of the i.i.d. matrix that matches the scaling `r` of the
symmetric Gaussian. -/
def vOf (r : ℝ) : ℝ≥0 := Real.toNNReal (r ^ 2 / 4)

/-- The variance of the symmetrised entry at `p`: `r²` on the diagonal, `r²/2` off it — Klartag's
`E Γ_ij ^ 2 = (1 + δ_ij)/n` after the scaling `r = √(2/n)`. -/
def varOf (r : ℝ) (p : UT n) : ℝ≥0 := Real.toNNReal ((r * cc p) ^ 2)

theorem coe_vOf (r : ℝ) : ((vOf r : ℝ≥0) : ℝ) = r ^ 2 / 4 :=
  Real.coe_toNNReal _ (by positivity)

theorem coe_varOf (r : ℝ) (p : UT n) : ((varOf r p : ℝ≥0) : ℝ) = (r * cc p) ^ 2 :=
  Real.coe_toNNReal _ (sq_nonneg _)

theorem map_phi (r : ℝ) (p : UT n) :
    (Measure.pi fun _ : Fin 2 => gaussianReal 0 (vOf r)).map (phi p)
      = gaussianReal 0 (varOf r p) := by
  classical
  set Q : Measure (Fin 2 → ℝ) := Measure.pi fun _ : Fin 2 => gaussianReal 0 (vOf r) with hQ
  have hev : ∀ k : Fin 2, HasLaw (fun z : Fin 2 → ℝ => z k) (gaussianReal 0 (vOf r)) Q :=
    fun k => (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 (vOf r)) k).hasLaw
  by_cases hd : p.1.1 = p.1.2
  · rw [phi_diag hd]
    have h : (fun z : Fin 2 → ℝ => 2 * z 0) = ((2 : ℝ) * ·) ∘ (fun z : Fin 2 → ℝ => z 0) := rfl
    rw [h, ← Measure.map_map (by fun_prop : Measurable fun x : ℝ => 2 * x)
      (measurable_pi_apply (0 : Fin 2)), (hev 0).map_eq, gaussianReal_map_const_mul]
    refine gaussianReal_ext_iff.2 ⟨by ring, ?_⟩
    refine NNReal.coe_injective ?_
    rw [NNReal.coe_mul, coe_vOf, coe_varOf, cc_diag hd]
    simp
    ring
  · rw [phi_offdiag hd]
    have hind : IndepFun (fun z : Fin 2 → ℝ => z 0) (fun z : Fin 2 → ℝ => z 1) Q := by
      have hpi := iIndepFun_pi (X := fun _ : Fin 2 => (id : ℝ → ℝ))
        (μ := fun _ : Fin 2 => gaussianReal 0 (vOf r)) (fun _ => aemeasurable_id)
      exact hpi.indepFun (by decide)
    have hsum := gaussianReal_add_gaussianReal_of_indepFun hind (hev 0) (hev 1)
    rw [show (fun z : Fin 2 → ℝ => z 0 + z 1)
        = (fun z : Fin 2 → ℝ => z 0) + (fun z : Fin 2 → ℝ => z 1) from rfl, hsum]
    refine gaussianReal_ext_iff.2 ⟨by ring, ?_⟩
    refine NNReal.coe_injective ?_
    rw [NNReal.coe_add, coe_vOf, coe_varOf]
    have hcc := cc_offdiag hd
    linear_combination (-(r ^ 2)) * hcc

theorem map_auxV (r : ℝ) :
    (auxMeasure n (vOf r)).map (fun ω : Aux n => fun p => phi p (ω p))
      = Measure.pi fun p : UT n => gaussianReal 0 (varOf r p) := by
  have hsf : ∀ p : UT n,
      SigmaFinite ((Measure.pi fun _ : Fin 2 => gaussianReal 0 (vOf r)).map (phi p)) := by
    intro p; rw [map_phi]; infer_instance
  rw [auxMeasure, Measure.pi_map_pi (fun p => (measurable_phi p).aemeasurable)]
  congr 1
  funext p
  exact map_phi r p

theorem map_ofLp_stdGaussian :
    (stdGaussian (EuclideanSpace ℝ (UT n))).map WithLp.ofLp
      = Measure.pi fun _ : UT n => gaussianReal 0 1 := by
  rw [← map_pi_eq_stdGaussian (ι := UT n), Measure.map_map (by fun_prop) (by fun_prop),
    show (WithLp.ofLp ∘ (WithLp.toLp 2 : (UT n → ℝ) → EuclideanSpace ℝ (UT n))) = id from rfl,
    Measure.map_id]

theorem map_coordVec {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (r : ℝ)
    {ξ : Ω → EuclideanSpace ℝ (UT n)} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ (UT n))) :
    P.map (fun ω => coordVec r (ξ ω)) = Measure.pi fun p : UT n => gaussianReal 0 (varOf r p) := by
  have hstep : (fun ω => coordVec r (ξ ω))
      = ((fun u : UT n → ℝ => fun p => (r * cc p) * u p) ∘ WithLp.ofLp) ∘ ξ := by
    funext ω p; simp only [coordVec, Function.comp_apply]
  have hmeas : Measurable fun u : UT n → ℝ => fun p : UT n => (r * cc p) * u p :=
    Measurable.of_eval fun p => (measurable_pi_apply p).const_mul _
  rw [hstep, ← Measure.map_map (hmeas.comp (WithLp.measurable_ofLp _ _)) hξ, hlaw,
    ← Measure.map_map hmeas (WithLp.measurable_ofLp _ _), map_ofLp_stdGaussian,
    Measure.pi_map_pi (fun p => (measurable_const_mul (r * cc p)).aemeasurable)]
  congr 1
  funext p
  rw [show (fun u : ℝ => (r * cc p) * u) = ((r * cc p) * ·) from rfl, gaussianReal_map_const_mul]
  refine gaussianReal_ext_iff.2 ⟨by ring, ?_⟩
  refine NNReal.coe_injective ?_
  rw [NNReal.coe_mul, coe_varOf]
  simp

/-- **The law of the symmetric Gaussian matrix is the law of `B + Bᵀ` with i.i.d. `B`.**  This is
Lemma 3.1's output in discrete form: it is what lets `GateL10.gaussian_opNormTail`, whose matrix is
`B + Bᵀ` with independent entries over the full product, be applied to the chain's increment, whose
entries above and below the diagonal are *equal* and therefore not independent. -/
theorem map_coordVec_eq_map_auxV {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (r : ℝ)
    {ξ : Ω → EuclideanSpace ℝ (UT n)} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ (UT n))) :
    P.map (fun ω => coordVec r (ξ ω))
      = (auxMeasure n (vOf r)).map (fun ω : Aux n => fun p => phi p (ω p)) := by
  rw [map_coordVec r hξ hlaw, map_auxV]

/-! ### The tail of the increment's operator norm -/

theorem measureReal_preimage {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A)
    {f : A → B} (hf : Measurable f) {S : Set B} (hS : MeasurableSet S) :
    μ.real (f ⁻¹' S) = (μ.map f).real S := by
  rw [measureReal_def, measureReal_def, Measure.map_apply hf hS]

theorem sqrt_coe_vOf {r : ℝ} (hr : 0 ≤ r) : Real.sqrt ((vOf r : ℝ≥0) : ℝ) = r / 2 := by
  rw [coe_vOf, show r ^ 2 / 4 = (r / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]

theorem vOf_pos {r : ℝ} (hr : 0 < r) : 0 < vOf r :=
  Real.toNNReal_pos.2 (by positivity)

/-- **Klartag, Corollary 3.2, for the discrete chain's increment.**  If `ξ` is a standard Gaussian
on the model `EuclideanSpace ℝ (UT n)` of `R^{n×n}_sym`, then the symmetric matrix `r · symMat ξ`
— which is the increment of the Dyson walk after time `r²`, `E (W_t)_ij² = t (1 + δ_ij)/2` —
satisfies, for every `s ≥ 1`,

`P(‖r · symMat ξ‖_op ≥ 6 r s √n) ≤ 4 exp (-s² n)`.

The proof runs `GateL10.gaussian_opNormTail` on the auxiliary i.i.d. space and transports the
conclusion along `map_coordVec_eq_map_auxV`. -/
theorem increment_opNorm_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {r : ℝ} (hr : 0 < r)
    {ξ : Ω → EuclideanSpace ℝ (UT n)} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ (UT n))) (s : ℝ) (hs : 1 ≤ s) :
    P.real {ω | 6 * r * s * Real.sqrt n ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (r • symMat (ξ ω))‖} ≤ 4 * Real.exp (-(s ^ 2 * n)) := by
  classical
  set thr : ℝ := 6 * r * s * Real.sqrt n with hthr
  set S : Set (UT n → ℝ) :=
    {u | thr ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (mkMat u)‖} with hS
  have hSmeas : MeasurableSet S := measurableSet_le measurable_const measurable_opNorm_mkMat
  have hset : {ω | thr ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (r • symMat (ξ ω))‖}
      = (fun ω => coordVec r (ξ ω)) ⁻¹' S := by
    ext ω; simp only [hS, Set.mem_ofPred_eq, Set.mem_preimage, smul_symMat_eq_mkMat]
  have hmeas : Measurable fun ω => coordVec r (ξ ω) := (measurable_coordVec r).comp hξ
  have hauxmeas : Measurable fun ω : Aux n => fun p => phi p (ω p) :=
    Measurable.of_eval fun p => (measurable_phi p).comp (measurable_pi_apply p)
  have hstep : P.real {ω | thr ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (r • symMat (ξ ω))‖}
      = (auxMeasure n (vOf r)).real ((fun ω : Aux n => fun p => phi p (ω p)) ⁻¹' S) := by
    rw [hset, measureReal_preimage P hmeas hSmeas, map_coordVec_eq_map_auxV r hξ hlaw,
      ← measureReal_preimage _ hauxmeas hSmeas]
  have hset2 : ((fun ω : Aux n => fun p => phi p (ω p)) ⁻¹' S)
      = {ω : Aux n | 12 * Real.sqrt ((vOf r : ℝ≥0) : ℝ) * s * Real.sqrt n ≤
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (auxB ω + (auxB ω)ᵀ)‖} := by
    ext ω
    simp only [hS, Set.mem_preimage, Set.mem_ofPred_eq, auxB_add_transpose ω]
    rw [sqrt_coe_vOf hr.le, hthr]
    constructor <;> intro h <;> linarith [h]
  rw [hstep, hset2]
  exact GateL10.gaussian_opNormTail (auxMeasure n (vOf r)) n auxB (vOf r) (vOf_pos hr)
    (auxB_indep _) (auxB_law _) s hs

/-- **The GOE normalisation.**  At `r = √(2/n)` the matrix `r · symMat ξ` is exactly Klartag's
`Γ` (`E Γ_ij ^ 2 = (1 + δ_ij)/n`), and the bound is his
`P(‖Γ‖_op ≥ C s) ≤ 4 exp (-s² n)` with `C = 6√2`. -/
theorem goe_opNorm_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hn : 0 < n)
    {ξ : Ω → EuclideanSpace ℝ (UT n)} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ (UT n))) (s : ℝ) (hs : 1 ≤ s) :
    P.real {ω | 6 * Real.sqrt 2 * s ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Real.sqrt (2 / n) • symMat (ξ ω))‖}
      ≤ 4 * Real.exp (-(s ^ 2 * n)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hrpos : 0 < Real.sqrt (2 / n) := Real.sqrt_pos.2 (by positivity)
  have hkey : 6 * Real.sqrt (2 / n) * s * Real.sqrt n = 6 * Real.sqrt 2 * s := by
    have h1 : Real.sqrt (2 / (n : ℝ)) * Real.sqrt (n : ℝ) = Real.sqrt 2 := by
      rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀]
      exact ne_of_gt hn0
    calc 6 * Real.sqrt (2 / n) * s * Real.sqrt n
        = 6 * s * (Real.sqrt (2 / n) * Real.sqrt n) := by ring
      _ = 6 * s * Real.sqrt 2 := by rw [h1]
      _ = 6 * Real.sqrt 2 * s := by ring
  have h := increment_opNorm_tail (n := n) hrpos hξ hlaw s hs
  rwa [hkey] at h

end GOE

end

end Submission.L10.Increments
