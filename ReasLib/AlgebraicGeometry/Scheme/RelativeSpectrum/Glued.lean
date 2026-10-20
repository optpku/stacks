module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Realization

/-!
# The relative spectrum glued from affine section spectra

The affine-open section spectra form an equifibered diagram over the native
directed affine cover. Its scheme colimit and structure morphism supply an
equipped realization, including actual identifications with the affine pieces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- The section spectra and restriction maps over the directed affine-open cover. -/
def relativeSpectrumNativeGluingData (A : S.QcAlgebraUnder) :
    S.directedAffineCover.RelativeGluingData where
  functor :=
    { obj := fun (U : S.affineOpens) ↦ Spec (qcAlgebraSectionRing A U)
      map := fun {U V : S.affineOpens} h ↦
        Spec.map (qcAlgebraSectionRestrict A (leOfHom h))
      map_id := sorry
      map_comp := sorry }
  natTrans :=
    { app := fun (U : S.affineOpens) ↦
        Spec.map (qcAlgebraStructureMap A U) ≫ U.2.isoSpec.inv
      naturality := sorry }
  equifibered := fun {U V : S.affineOpens} h ↦
    isPullback_specMap_qcAlgebraSectionRestrict A U.2 V.2 (leOfHom h)

/-- The glued relative spectrum restricts to the specified section spectrum on each affine open.
The maps are the native open-image identification of the corresponding colimit injection. -/
def relativeSpectrumGluedLocalIso (A : S.QcAlgebraUnder) (U : S.affineOpens) :
    ((relativeSpectrumNativeGluingData A).toBase ⁻¹ᵁ (U : S.Opens)).toScheme ≅
      Spec (qcAlgebraSectionRing A U) :=
  (relativeSpectrumNativeGluingData A).glued.isoOfEq
      (by
        have h := (relativeSpectrumNativeGluingData A).toBase_preimage_eq_opensRange_ι U
        change (relativeSpectrumNativeGluingData A).toBase ⁻¹ᵁ
            (U : S.Opens).ι.opensRange = _ at h
        rw [Scheme.Opens.opensRange_ι] at h
        exact h) ≪≫
    (colimit.ι (relativeSpectrumNativeGluingData A).functor U).isoOpensRange.symm

/-- A concrete relative-spectrum realization built from affine section spectra. -/
def relativeSpectrumRealization (A : S.QcAlgebraUnder) : RelativeSpectrumRealization A where
  Y := (relativeSpectrumNativeGluingData A).glued
  toBase := (relativeSpectrumNativeGluingData A).toBase
  localIso := relativeSpectrumGluedLocalIso A
  localIso_hom_over := sorry
  localTransition := sorry

/-- The structural morphism is the actual cocone descent of the affine structure maps. -/
theorem relativeSpectrumRealization_toBase (A : S.QcAlgebraUnder) :
    (relativeSpectrumRealization A).toBase =
      (relativeSpectrumNativeGluingData A).toBase := rfl

/-- The inverse local identification followed by the open inclusion is the colimit injection. -/
theorem relativeSpectrumGluedLocalIso_inv_ι (A : S.QcAlgebraUnder) (U : S.affineOpens) :
    (relativeSpectrumGluedLocalIso A U).inv ≫
        ((relativeSpectrumNativeGluingData A).toBase ⁻¹ᵁ (U : S.Opens)).ι =
      colimit.ι (relativeSpectrumNativeGluingData A).functor U := sorry

/-- The constructed scheme has the affine-local relative-spectrum realization property. -/
theorem relativeSpectrumRealization_realizes (A : S.QcAlgebraUnder) :
    realizesRelativeSpectrum A (relativeSpectrumRealization A).toBase :=
  RelativeSpectrumRealization.realizes (relativeSpectrumRealization A)

end AlgebraicGeometry.Scheme
