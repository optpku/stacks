module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback

/-!
# Affine étale pullback

This file constructs affine étale base change along affine morphisms and its
comparison with ordinary étale pullback.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.AffineEtale

variable {S T : Scheme.{u}}

/-- The affine étale object obtained by base change along an affine morphism. -/
noncomputable def pullbackObj (f : T ⟶ S) [IsAffineHom f] (U : S.AffineEtale) :
    T.AffineEtale :=
  let h_affine : IsAffine (CategoryTheory.Limits.pullback U.hom f) :=
    @isAffine_of_isAffineHom _ _ (CategoryTheory.Limits.pullback.fst U.hom f)
      (MorphismProperty.pullback_fst _ _ (show IsAffineHom f from inferInstance))
      (isAffine_Spec _)
  let h_iso : Etale (@Scheme.isoSpec _ h_affine).inv :=
    MorphismProperty.of_isIso @Etale _
  let h_snd : Etale (CategoryTheory.Limits.pullback.snd U.hom f) :=
    MorphismProperty.pullback_snd _ _ U.prop
  let h_map : Etale
      ((@Scheme.isoSpec _ h_affine).inv ≫ CategoryTheory.Limits.pullback.snd U.hom f) :=
    MorphismProperty.comp_mem @Etale _ _ h_iso h_snd
  @AffineEtale.mk _ _
    ((@Scheme.isoSpec _ h_affine).inv ≫ CategoryTheory.Limits.pullback.snd U.hom f) h_map

/-- The morphism of spectra underlying affine étale base change. -/
noncomputable def pullbackMapScheme (f : T ⟶ S) [IsAffineHom f]
    {U V : S.AffineEtale} (g : U ⟶ V) :
    Spec Γ(CategoryTheory.Limits.pullback U.hom f, ⊤) ⟶
      Spec Γ(CategoryTheory.Limits.pullback V.hom f, ⊤) :=
  let hU : IsAffine (CategoryTheory.Limits.pullback U.hom f) :=
    @isAffine_of_isAffineHom _ _ (CategoryTheory.Limits.pullback.fst U.hom f)
      (MorphismProperty.pullback_fst _ _ (show IsAffineHom f from inferInstance))
      (isAffine_Spec _)
  let hV : IsAffine (CategoryTheory.Limits.pullback V.hom f) :=
    @isAffine_of_isAffineHom _ _ (CategoryTheory.Limits.pullback.fst V.hom f)
      (MorphismProperty.pullback_fst _ _ (show IsAffineHom f from inferInstance))
      (isAffine_Spec _)
  (@Scheme.isoSpec _ hU).inv ≫
    CategoryTheory.Limits.pullback.map U.hom f V.hom f (Scheme.Spec.map g.left) (𝟙 T) (𝟙 S)
      ((Category.comp_id U.hom).trans g.w.symm)
      ((Category.comp_id f).trans (Category.id_comp f).symm) ≫
    (@Scheme.isoSpec _ hV).hom

/-- The spectrum morphism of `pullbackMapScheme` commutes with the structure morphisms to `T`. -/
theorem pullbackMapScheme_over (f : T ⟶ S) [IsAffineHom f]
    {U V : S.AffineEtale} (g : U ⟶ V) :
    Scheme.Spec.map (Scheme.Spec.preimage (pullbackMapScheme f g)) ≫
        (pullbackObj f V).hom =
      (pullbackObj f U).hom := sorry

/-- The morphism obtained by affine étale base change. -/
noncomputable def pullbackMap (f : T ⟶ S) [IsAffineHom f]
    {U V : S.AffineEtale} (g : U ⟶ V) :
    pullbackObj f U ⟶ pullbackObj f V :=
  MorphismProperty.CostructuredArrow.homMk
    (Scheme.Spec.preimage (pullbackMapScheme f g)) trivial
    (pullbackMapScheme_over f g)

/-- Affine étale base change preserves identity morphisms. -/
theorem pullbackMap_id (f : T ⟶ S) [IsAffineHom f] (U : S.AffineEtale) :
    pullbackMap f (𝟙 U) = 𝟙 (pullbackObj f U) := sorry

/-- Affine étale base change preserves composition. -/
theorem pullbackMap_comp (f : T ⟶ S) [IsAffineHom f]
    {U V W : S.AffineEtale} (g : U ⟶ V) (h : V ⟶ W) :
    pullbackMap f (g ≫ h) = pullbackMap f g ≫ pullbackMap f h := sorry

/-- Base change along an affine morphism on affine étale sites. -/
noncomputable def pullback (f : T ⟶ S) [IsAffineHom f] :
    S.AffineEtale ⥤ T.AffineEtale where
  obj := pullbackObj f
  map := pullbackMap f
  map_id := pullbackMap_id f
  map_comp := pullbackMap_comp f

/-- The comparison at an affine étale object between ordinary and affine étale pullback. -/
noncomputable def pullbackSpecIsoApp (f : T ⟶ S) [IsAffineHom f]
    (U : S.AffineEtale) :
    (AffineEtale.Spec S ⋙ smallEtalePullback f).obj U ≅
      (pullback f ⋙ AffineEtale.Spec T).obj U :=
  let h_affine : IsAffine (CategoryTheory.Limits.pullback U.hom f) :=
    @isAffine_of_isAffineHom _ _ (CategoryTheory.Limits.pullback.fst U.hom f)
      (MorphismProperty.pullback_fst _ _ (show IsAffineHom f from inferInstance))
      (isAffine_Spec _)
  MorphismProperty.Over.isoMk
    (@Scheme.isoSpec _ h_affine) sorry

/-- The natural comparison between ordinary and affine étale pullback. -/
noncomputable def pullbackSpecIso (f : T ⟶ S) [IsAffineHom f] :
    AffineEtale.Spec S ⋙ smallEtalePullback f ≅
      pullback f ⋙ AffineEtale.Spec T :=
  NatIso.ofComponents (pullbackSpecIsoApp f) sorry

end AlgebraicGeometry.Scheme.AffineEtale
