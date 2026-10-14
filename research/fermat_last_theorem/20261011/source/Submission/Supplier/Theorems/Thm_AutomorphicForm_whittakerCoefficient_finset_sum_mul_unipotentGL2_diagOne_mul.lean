import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Probability.ConditionalProbability
import Submission.Supplier.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Submission.Supplier.Definitions.Def_NumberField_AdelicBox
import Submission.Supplier.Definitions.Def_NumberField_AdelicLevel
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicBox NumberField.AdelicHaar NumberField.AdelicLevel

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem AutomorphicForm.whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsPrincipalInvariantAddChar F ψ)
    (G : AdelicGL2 (𝓞 F) F → ℂ)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F) (h : AdelicGL2 (𝓞 F) F),
      G (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * h) = G (unipotentGL2 u * h))
    (ι : Finset (AdeleRing (𝓞 F) F)) (c : AdeleRing (𝓞 F) F → ℂ)
    (α : F) (a : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F)
    (hcomm : ∀ y ∈ ι, g * unipotentGL2 y = unipotentGL2 y * g)
    (hint : ∀ y ∈ ι, WhittakerCoefficientIntegrable F (productionPinsOf F D U gen (adelicBox F)) ψ
      (fun x => G (x * unipotentGL2 y)) α (diagOne a * g)) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ
        (fun x => ∑ y ∈ ι, c y * G (x * unipotentGL2 y)) α (diagOne a * g) =
      (∑ y ∈ ι, c y * ψ (algebraMap F (AdeleRing (𝓞 F) F) α * ((a : AdeleRing (𝓞 F) F) * y))) *
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ G α (diagOne a * g) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul.solution
