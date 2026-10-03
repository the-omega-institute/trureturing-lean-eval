import D5.S3.Factorization.Galois.GeneralPowerCharacterLayer
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open D5.S3.Factorization.Galois.GeneralPowerCharacterLayer

namespace LeanEval.NikolovSegalDependency

/- Submission dependency staging for the abelian case of the strong completeness
theorem, attributed to Nikolov–Segal, Annals of Mathematics 165 (2007),
Theorem 1.1, doi:10.4007/annals.2007.165.171. Not retained D5 content. -/

/-- The cyclic factor map determined by an element annihilated by `n`. -/
def cyclicPowerHom {Q : Type*} [CommGroup Q] (n : ℕ) (q : Q) (hq : q ^ n = 1) :
    Multiplicative (ZMod n) →* Q :=
  AddMonoidHom.toMultiplicativeLeft (ZMod.lift n ⟨zmultiplesHom (Additive Q) (.ofMul q), by
    change Additive.ofMul (q ^ (n : ℤ)) = 0
    simpa using congrArg Additive.ofMul hq⟩)

@[simp] theorem cyclicPowerHom_one {Q : Type*} [CommGroup Q]
    (n : ℕ) (q : Q) (hq : q ^ n = 1) :
    cyclicPowerHom n q hq (Multiplicative.ofAdd (1 : ZMod n)) = q := by
  simp only [cyclicPowerHom, AddMonoidHom.coe_toMultiplicativeLeft,
    Function.comp_apply]
  change Additive.toMul ((ZMod.lift n _) (1 : ZMod n)) = q
  rw [← Int.cast_one (R := ZMod n), ZMod.lift_coe]
  simp

/-- Finite products of cyclic factor maps. -/
def generatorProductHom {Q : Type*} [CommGroup Q] {ι : Type*} [Fintype ι]
    (n : ℕ) (q : ι → Q) (hq : ∀ i, q i ^ n = 1) :
    Multiplicative (ι → ZMod n) →* Q where
  toFun a := ∏ i, cyclicPowerHom n (q i) (hq i) (.ofAdd (a.toAdd i))
  map_one' := by simp
  map_mul' a b := by simp [Finset.prod_mul_distrib]

/-- A compact Hausdorff abelian group with `S` as dense generators has open
`n`th-power subgroup of index at most `n ^ S.card`. This dependency is not the
nonabelian Nikolov–Segal theorem. -/
theorem compact_abelian_power_quotient
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] (S : Finset G)
    (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤)
    (n : ℕ) (hn : 0 < n) :
    IsOpen ((powMonoidHom (α := G) n).range : Set G) ∧
      (powMonoidHom (α := G) n).range.index ≤ n ^ S.card := by
  classical
  let P := powerSubgroup G n
  have hP : IsClosed (P : Set G) := by
    change IsClosed (Set.range fun g : G => g ^ n)
    exact (isCompact_range ((continuous_id : Continuous (fun g : G => g)).pow n)).isClosed
  have : IsClosed (P : Set G) := hP
  have : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Q := G ⧸ P
  let f : G →* Q := QuotientGroup.mk' P
  have hf : Continuous f := QuotientGroup.continuous_mk
  have hq : ∀ q : Q, q ^ n = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (power_quotient_has_exponent_dividing G n)
  let F : Multiplicative (S → ZMod n) →* Q :=
    generatorProductHom n (fun s => f s.val) (fun s => hq (f s.val))
  have hFclosed : IsClosed (F.range : Set Q) := by
    change IsClosed (Set.range F)
    exact (Set.finite_range F).isClosed
  have hgen : Subgroup.closure (S : Set G) ≤ F.range.comap f := by
    apply (Subgroup.closure_le _).2
    intro g hg
    let s : S := ⟨g, hg⟩
    refine ⟨Multiplicative.ofAdd (Pi.single s 1), ?_⟩
    change (∏ i : S, cyclicPowerHom n (f i.val) _
      (.ofAdd ((Pi.single s (1 : ZMod n) : S → ZMod n) i))) = f g
    rw [Finset.prod_eq_single s]
    · simp [s]
    · intro b _ hbs
      simp [Pi.single_eq_of_ne hbs]
    · simp
  have hdense : ((Subgroup.closure (S : Set G)).map f).topologicalClosure = ⊤ :=
    (QuotientGroup.mk'_surjective P).denseRange.topologicalClosure_map_subgroup hf hS
  have hmap : (Subgroup.closure (S : Set G)).map f ≤ F.range :=
    (Subgroup.map_le_iff_le_comap).mpr hgen
  have htop : F.range = ⊤ := by
    apply top_unique
    rw [← hdense]
    exact Subgroup.topologicalClosure_minimal _ hmap hFclosed
  have hsurj : Function.Surjective F := MonoidHom.range_eq_top.mp htop
  have : Finite Q := Finite.of_surjective F hsurj
  have : P.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  constructor
  · exact P.isOpen_of_isClosed_of_finiteIndex hP
  · change Nat.card Q ≤ n ^ S.card
    calc
      Nat.card Q ≤ Nat.card (Multiplicative (S → ZMod n)) :=
        Nat.card_le_card_of_surjective F hsurj
      _ = n ^ S.card := by simp [Nat.card_eq_fintype_card]

#print axioms cyclicPowerHom
#print axioms cyclicPowerHom_one
#print axioms generatorProductHom
#print axioms compact_abelian_power_quotient

end LeanEval.NikolovSegalDependency
