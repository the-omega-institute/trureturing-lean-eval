import Mathlib
import Submission.Supplier.Definitions.Def_ModularForm_HeckeOperatorForms
import Submission.Supplier.Definitions.Def_Gamma0CoeffCohomology
import Submission.Supplier.Definitions.Def_HeckeEis_BinaryFormRep
import Submission.Supplier.Definitions.Def_Gamma0CoeffCohomologyEigen
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_HeckeEis_isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-simp] HeckeEis.coe_linePow

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Set ℕ) (n : ℕ) (k : ℤ) (hk : (n : ℤ) + 2 = k)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0)
    (a : ℕ → integralClosure ℤ ℂ)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      ModularForm.heckeTLin k hℓ hℓN f = ((a ℓ : integralClosure ℤ ℂ) : ℂ) • f)
    (κ : Type) [Field κ] [CharP κ p] (φ : integralClosure ℤ ℂ →+* κ) :
    HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S (fun ℓ => φ (a ℓ)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul.solution

#print axioms HeckeEis.isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul
