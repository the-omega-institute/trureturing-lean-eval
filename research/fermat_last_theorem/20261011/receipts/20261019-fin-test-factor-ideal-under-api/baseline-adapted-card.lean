import Submission.Supplier.Definitions.Def_AutomorphicForm_TwistedOrbital
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem AutomorphicForm.exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f)
    (hlev : ∀ g : AdelicGL2 (𝓞 L) L,
      ∀ k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
        f (g * k) = f g)
    (harch : f ∈ archCutSubmodule L tys) :
    ∃ (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ) (fa : ℕ → (GL (Fin 2) (InfiniteAdeleRing L) → ℂ)),
      IsFinTestFactor L ff ∧
      (∀ x : AdelicGL2 (𝓞 L) L, ff (glFin (𝓞 L) L x) ≠ 0 → ∃ a k : AdelicGL2 (𝓞 L) L,
        glFin (𝓞 L) L a = 1 ∧
        k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L ∧ x = a * k) ∧
      (∀ n, IsArchTestFactor L (fa n)) ∧
      (∀ n, IsUnitFactorizableAboveOfType K L tys
        (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK
        (fun g => fa n (glArch (𝓞 L) L g) * ff (glFin (𝓞 L) L g))) ∧
      ∀ g, Filter.Tendsto
        (fun n => rightConv L f (fun x => fa n (glArch (𝓞 L) L x) * ff (glFin (𝓞 L) L x)) g)
        Filter.atTop (nhds (f g)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule.solution
