module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Sections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Scheme-theoretic images of sections over open subschemes

The scheme-theoretic image of a section of a separated morphism agrees with the target over
every retrocompact open on which the section is defined.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

noncomputable section

/-- Let `s : V ⟶ X` be a section over a retrocompact open `V` of a separated morphism
`f : X ⟶ Y`. The scheme-theoretic image of `s` maps isomorphically to `Y` over `V`. -/
@[stacks 0CNG]
theorem schemeTheoreticImage_section_restrict_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] (V : Y.Opens)
    (hVretro : IsRetrocompact (V : Set Y)) (s : (V : Scheme.{u}) ⟶ X)
    (hs : s ≫ f = V.ι) :
    IsIso ((Scheme.Hom.imageι s ≫ f) ∣_ V) := by
  let W := f ⁻¹ᵁ V
  let t : (V : Scheme.{u}) ⟶ (W : Scheme.{u}) :=
    pullback.lift s (𝟙 _) (by simpa using hs) ≫
      (pullbackRestrictIsoRestrict f V).hom
  have htsection : t ≫ (f ∣_ V) = 𝟙 _ := by
    simp only [t, Category.assoc,
      pullbackRestrictIsoRestrict_hom_morphismRestrict, pullback.lift_snd]
  have htι : t ≫ W.ι = s := by
    change t ≫ (f ⁻¹ᵁ V).ι = s
    simp only [t, Category.assoc, pullbackRestrictIsoRestrict_hom_ι,
      pullback.lift_fst]
  have hsW : s ⁻¹ᵁ W = ⊤ := by
    dsimp only [W]
    rw [← Scheme.Hom.comp_preimage, hs]
    simp
  -- Local instance justification (proof-local temporary data): infer quasi-compactness after restricting along the retrocompact open inclusion.
  haveI : QuasiCompact V.ι :=
    quasiCompact_iff_isSpectralMap.mpr
      (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hVretro)
  -- Local instance justification (proof-local temporary data): transport quasi-compactness to the pullback open inclusion defining W.
  haveI : QuasiCompact W.ι :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (isPullback_morphismRestrict f V) inferInstance
  -- Local instance justification (proof-local temporary data): register quasi-compactness of the section t for the local factorization.
  haveI : QuasiCompact t := Scheme.Hom.Section.quasiCompact htsection
  -- Local instance justification (proof-local temporary data): infer quasi-compactness of s from its factorization through t and W.ι.
  haveI : QuasiCompact s := by
    rw [← htι]
    infer_instance
  -- Local instance justification (proof-local temporary data): identify the inclusion of the top preimage open as an isomorphism.
  haveI : IsIso (s ⁻¹ᵁ W).ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simpa using hsW)
  -- Local instance justification (proof-local temporary data): use the isomorphism of the top open inclusion as a closed immersion.
  haveI : IsClosedImmersion
      ((s ⁻¹ᵁ W).ι : (s ⁻¹ᵁ W).toScheme ⟶ (V : Scheme.{u})) :=
    inferInstance
  have hrestrict : s ∣_ W = (s ⁻¹ᵁ W).ι ≫ t := by
    rw [← cancel_mono W.ι, morphismRestrict_ι, Category.assoc, htι]
  -- Local instance justification (proof-local temporary data): register the separated morphism section t as a closed immersion.
  haveI : IsClosedImmersion t := Scheme.Hom.Section.isClosedImmersion htsection
  -- Local instance justification (proof-local temporary data): infer that the restricted section is a composite of closed immersions.
  haveI : IsClosedImmersion (s ∣_ W) := by
    rw [hrestrict]
    exact IsClosedImmersion.comp _ _
  have hrsection : (s ∣_ W) ≫ (f ∣_ V) = (s ⁻¹ᵁ W).ι := by
    rw [hrestrict, Category.assoc, htsection, Category.comp_id]
  -- Local instance justification (proof-local temporary data): infer the local image composite is an isomorphism from its factorization through the top open inclusion.
  haveI : IsIso ((s ∣_ W).imageι ≫ (f ∣_ V)) := by
    apply IsIso.of_isIso_fac_left
      (f := (s ∣_ W).toImage)
      (g := (s ∣_ W).imageι ≫ (f ∣_ V))
      (h := (s ⁻¹ᵁ W).ι)
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hrsection]
  have hlocal : IsIso ((s.imageι ∣_ W) ≫ (f ∣_ V)) := by
    rw [← isIso_comp_left_iff
      (Scheme.Hom.imageMorphismRestrictIso s W).hom
      ((s.imageι ∣_ W) ≫ (f ∣_ V))]
    rw [← Category.assoc, Scheme.Hom.imageMorphismRestrictIso_hom_imageι]
    infer_instance
  have hcomp := morphismRestrict_comp s.imageι f V
  exact hcomp.symm ▸ hlocal

end


end AlgebraicGeometry
