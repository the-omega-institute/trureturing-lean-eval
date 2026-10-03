import AbelianPowerQuotient
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Topology.Connected.TotallyDisconnected

open scoped BigOperators
open LeanEval.NikolovSegalDependency

-- The finite products in the index equality test have exactly `d` dense generators.
example (n d : ℕ) (hn : 1 < n) :
    ∃ S : Finset (Fin d → Multiplicative (ZMod n)),
      S.card = d ∧ Subgroup.closure (S : Set (Fin d → Multiplicative (ZMod n))) = ⊤ := by
  classical
  have : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  have : Fact (1 < n) := ⟨hn⟩
  let b : Fin d → (Fin d → Multiplicative (ZMod n)) :=
    fun i => Pi.mulSingle i (.ofAdd 1)
  let S : Finset (Fin d → Multiplicative (ZMod n)) := Finset.univ.image b
  have hb : Function.Injective b := by
    intro i j h
    by_contra hij
    have hc := congrFun h i
    have hz : (1 : ZMod n) = 0 := by
      simpa [b, Pi.mulSingle_apply, hij, Ne.symm hij] using
        congrArg Multiplicative.toAdd hc
    exact one_ne_zero hz
  refine ⟨S, ?_, ?_⟩
  · simp [S, Finset.card_image_of_injective _ hb]
  · apply top_unique
    intro g _
    let C := Subgroup.closure (S : Set (Fin d → Multiplicative (ZMod n)))
    have hbi (i : Fin d) : b i ∈ C :=
      Subgroup.subset_closure (by simp [S])
    have hg (i : Fin d) : b i ^ (g i).toAdd.val = Pi.mulSingle i (g i) := by
      dsimp [b]
      rw [← Pi.mulSingle_pow]
      congr 1
      apply Multiplicative.toAdd.injective
      simp [toAdd_pow, nsmul_eq_mul]
    rw [← Finset.univ_prod_mulSingle g]
    apply C.prod_mem
    intro i _
    rw [← hg i]
    exact C.pow_mem (hbi i) _

-- The abelian specialization also derives Hausdorffness from the exact official
-- totally disconnected hypothesis; no extra Hausdorff premise is inserted.
example (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : ∃ S : Finset G, (Subgroup.closure (S : Set G)).topologicalClosure = ⊤)
    (H : Subgroup G) [H.FiniteIndex] : IsOpen (H : Set G) := by
  have : T2Space G := IsTopologicalGroup.t2Space_iff_one_closed.mpr
    (by simpa using (isClosed_connectedComponent (x := (1 : G))))
  obtain ⟨S, hS⟩ := hG
  have hpow := (compact_abelian_power_quotient G S hS H.index
    (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)).1
  apply Subgroup.isOpen_mono (H₁ :=
    D5.S3.Factorization.Galois.GeneralPowerCharacterLayer.powerSubgroup G H.index) ?_ hpow
  apply (D5.S3.Factorization.Galois.GeneralPowerCharacterLayer.power_subgroup_le_iff_quotient_pow_eq_one
    G H.index H).2
  exact fun q => pow_card_eq_one'
