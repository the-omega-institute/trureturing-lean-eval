/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.

Uses the proved Hausdorff–Alexandroff and local-surjectivity suppliers in
CWComparison.SimplexCover; no continuous section is assumed.
-/
import CWComparison.SimplexCover
import Mathlib.Condensed.Light.EffectiveEpi

noncomputable section
open CategoryTheory Limits LightCondensed TopologicalSpace

namespace CWComparison

/-- A genuine compact metrizable surjection induces a sheaf epimorphism even
when its source is not totally disconnected. This will descend shrinking edges. -/
theorem compactCover_condensed_epi {K X : TopCat.{0}} [CompactSpace K]
    [MetrizableSpace K] [T2Space X] (f : K ⟶ X) (hf : Function.Surjective f) :
    Epi (topCatToLightCondSet.map f) := by
  classical
  by_cases hk : Nonempty K
  · letI : Nonempty K := hk
    let c := compactMetrizableCover K
    have hc : Function.Surjective (f.hom.comp c) :=
      hf.comp (compactMetrizableCover_surjective K)
    have : Epi (topCatToLightCondSet.map (TopCat.ofHom (f.hom.comp c))) :=
      profiniteCover_condensed_epi (X := X) _ hc
    have : Epi (topCatToLightCondSet.map (TopCat.ofHom c) ≫
        topCatToLightCondSet.map f) := by
      rw [← Functor.map_comp]
      exact ‹Epi (topCatToLightCondSet.map (TopCat.ofHom (f.hom.comp c)))›
    exact epi_of_epi (topCatToLightCondSet.map (TopCat.ofHom c))
      (topCatToLightCondSet.map f)
  · letI : IsEmpty K := not_nonempty_iff.mp hk
    have hx : IsEmpty X := ⟨fun x => by obtain ⟨k, _⟩ := hf x; exact isEmptyElim k⟩
    letI : IsEmpty X := hx
    have : IsIso f := by
      let e : K ≅ X := {
        hom := f
        inv := TopCat.ofHom ⟨fun x => isEmptyElim x, continuous_of_discreteTopology⟩
        hom_inv_id := by ext k; exact isEmptyElim k
        inv_hom_id := by ext x; exact isEmptyElim x }
      exact e.isIso_hom
    infer_instance

end CWComparison
