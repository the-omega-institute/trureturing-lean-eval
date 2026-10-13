import Definitions.Def_DedekindDomain_IntegralClosure
import P2M.Util
import P2M.Sol.S_NumberField_exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one
    (K : Type) [Field K] [NumberField K] (hK : 2 ≤ Module.finrank ℚ K)
    (F : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))) :
    ∃ (p₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (w₀ w₂ : p₀.Extension (𝓞 K)),
      p₀ ∉ F ∧ w₀.1 ≠ w₂.1 ∧
      P2MW.S_NumberField_exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one.quotientInertiaDeg p₀.asIdeal w₀.1.asIdeal = 1 ∧
      ∀ w : p₀.Extension (𝓞 K), Ideal.ramificationIdx' p₀.asIdeal w.1.asIdeal = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one.solution

run_cmd Lean.Elab.Command.liftTermElabM do
  let replacementName := `P2MW.S_NumberField_exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one.quotientInertiaDeg
  let originalName := `Ideal.inertiaDeg'
  let replacement ← Lean.Meta.mkConstWithFreshMVarLevels replacementName
  let original ← Lean.Meta.mkConstWithFreshMVarLevels originalName
  unless ← Lean.Meta.withTransparency .all (Lean.Meta.isDefEq replacement original) do
    throwError "The quotient inertia definition changed"
  let ty := (← Lean.getConstInfo `NumberField.exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one).type
  let originalTy := ty.replace fun e => match e with
    | .const n levels => if n == replacementName then some (.const originalName levels) else none
    | _ => none
  unless ← Lean.Meta.isDefEq ty originalTy do
    throwError "The original final theorem type changed"
  Lean.logInfo "Original quotient inertia definition and final theorem type preserved"

#print axioms NumberField.exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one
