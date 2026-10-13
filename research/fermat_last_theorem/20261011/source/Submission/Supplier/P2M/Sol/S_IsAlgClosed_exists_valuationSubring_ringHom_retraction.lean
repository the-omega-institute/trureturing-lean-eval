import Mathlib
import Submission.Supplier.Theorems.Thm_ValuationSubring_exists_ringHom_extend_of_isAlgClosed
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_IsAlgClosed_exists_valuationSubring_ringHom_retraction

set_option autoImplicit false

theorem solution
    (K K' : Type*) [Field K] [IsAlgClosed K] [Field K'] [Algebra K K'] :
    ∃ (A : ValuationSubring K') (hK : ∀ c : K, algebraMap K K' c ∈ A) (σ : A →+* K),
      RingHom.ker σ = IsLocalRing.maximalIdeal A ∧
      ∀ c : K, σ ⟨algebraMap K K' c, hK c⟩ = c := by
  let f : K →+* K' := algebraMap K K'
  let e : K ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun a b h => f.injective (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  obtain ⟨O, hRO, ψ, hψ, hker⟩ :=
    ValuationSubring.exists_ringHom_extend_of_isAlgClosed (Ω := K) f.range e.symm.toRingHom
  refine ⟨O, fun c => hRO ⟨c, rfl⟩, ψ, hker, fun c => ?_⟩
  have h1 : ψ (Subring.inclusion hRO ⟨f c, ⟨c, rfl⟩⟩) = e.symm ⟨f c, ⟨c, rfl⟩⟩ := by
    rw [← RingHom.comp_apply, hψ]; rfl
  have h2 : e.symm ⟨f c, ⟨c, rfl⟩⟩ = c := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  rw [h2] at h1
  exact h1
