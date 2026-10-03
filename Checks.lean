import AbelianPowerQuotient

open D5.S3.Factorization.Galois.GeneralPowerCharacterLayer
open LeanEval.NikolovSegalDependency

-- Positive powers with a singleton exponent give the full power subgroup.
example (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] (S : Finset G)
    (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤) :
    IsOpen ((powMonoidHom (α := G) 1).range : Set G) ∧
      (powMonoidHom (α := G) 1).range.index ≤ 1 := by
  simpa using compact_abelian_power_quotient G S hS 1 (by decide)

-- No abstract generators plus density forces every positive power index to be at most one.
example (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    (hS : (Subgroup.closure (∅ : Set G)).topologicalClosure = ⊤)
    (n : ℕ) (hn : 0 < n) :
    IsOpen ((powMonoidHom (α := G) n).range : Set G) ∧
      (powMonoidHom (α := G) n).range.index ≤ 1 := by
  simpa using compact_abelian_power_quotient G ∅ (by simpa using hS) n hn

-- Finite products of cyclic groups attain the cardinal bound for `d` generators.
example (n d : ℕ) :
    (powMonoidHom (α := Fin d → Multiplicative (ZMod n)) n).range.index = n ^ d := by
  have hp : (powMonoidHom (α := Fin d → Multiplicative (ZMod n)) n).range = ⊥ := by
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      rw [Subgroup.mem_bot]
      funext i
      apply Multiplicative.toAdd.injective
      change n • (g i).toAdd = 0
      simp [nsmul_eq_mul]
    · exact bot_le
  rw [hp, Subgroup.index_bot]
  rw [Nat.card_fun, Nat.card_congr
    (Multiplicative.toAdd : Multiplicative (ZMod n) ≃ ZMod n)]
  simp

-- The abelian finite-index specialization is an application, not a retained wrapper.
example (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    (hG : ∃ S : Finset G, (Subgroup.closure (S : Set G)).topologicalClosure = ⊤)
    (H : Subgroup G) [H.FiniteIndex] : IsOpen (H : Set G) := by
  obtain ⟨S, hS⟩ := hG
  have hpow := (compact_abelian_power_quotient G S hS H.index
    (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)).1
  apply Subgroup.isOpen_mono (H₁ := powerSubgroup G H.index) ?_ hpow
  apply (power_subgroup_le_iff_quotient_pow_eq_one G H.index H).2
  exact fun q => pow_card_eq_one'
