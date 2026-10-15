import Mathlib
import Submission.Supplier.Definitions.Def_GaloisRep_Flat
import Submission.Supplier.Theorems.Thm_HopfAlgebra_exists_signTwist_linearEquiv_padicInt_of_odd
import Submission.Supplier.Theorems.Thm_HopfAlgebra_exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_HopfAlgebra_exists_signTwist_withConv_mulEquiv_padicInt_of_odd_of_not_isSquare

open scoped NNReal

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d : ℚ_[p]) (hd : ‖d‖₊ = 1) (hd_nsq : ¬ IsSquare d)
    (s : AlgebraicClosure ℚ_[p]) (hs : s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hfin : Module.Finite ℤ_[p] H) (hflat : Module.Flat ℤ_[p] H)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra ℤ_[p] H'),
      Module.Finite ℤ_[p] H' ∧ Module.Flat ℤ_[p] H' ∧ Coalgebra.IsCocomm ℤ_[p] H' ∧
      ∃ β : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
            WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
        (∀ f' g', β (f' * g') = β f' * β g') ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f' g' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]))
          (g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ h' : H', g' h' = σ (f' h')) →
          (∀ h : H, g h = σ ((β f') h)) →
            (σ s = s → β g' = g) ∧ (σ s ≠ s → β g' * g = 1) := by

  have hd' : ‖d‖ = 1 := by
    have : ((‖d‖₊ : ℝ≥0) : ℝ) = ((1 : ℝ≥0) : ℝ) := by exact_mod_cast hd
    simpa [coe_nnnorm] using this

  let d₀ : ℤ_[p] := ⟨d, hd'.le⟩
  have hd₀d : (d₀ : ℚ_[p]) = d := rfl
  have hd₀u : IsUnit d₀ := by
    rw [PadicInt.isUnit_iff]
    simpa [d₀, PadicInt.norm_eq_padic_norm] using hd'

  obtain ⟨H', _, _, hfin', hflat', hcocomm', e, he1, hemul, hecounit, heant, hecomul⟩ :=
    HopfAlgebra.exists_signTwist_linearEquiv_padicInt_of_odd p hp2 d₀ hd₀u
      H hfin hflat hcocomm

  obtain ⟨β, hβmul, hβtwist⟩ :=
    HopfAlgebra.exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt p hp2
      d hd hd_nsq s hs d₀ hd₀d hd₀u
      H hfin hflat hcocomm H' hfin' hflat' hcocomm'
      e he1 hemul hecounit heant hecomul
  exact ⟨H', _, _, hfin', hflat', hcocomm', β, hβmul, hβtwist⟩
