/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Basic
public import ReasLib.CategoryTheory.Sites.Ringed.Map

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.RingedSite.Localization


@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

variable {Y : AlgebraicSpace S} {U : Over S}

/-- A morphism in the slice `Y_étale / f` remains étale over the scheme `ofOver U`. -/
instance etale_ofOverMap_of_slice (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (smallEtaleSite.mk f (hφ := inferInstance))) :
    Etale (ofOverMap (W.hom.left : W.left.left ⟶ U)) :=
  sorry

/-- Recovering a scheme map respects the triangle after étale postcomposition. -/
private theorem etaleLocalizationHom_w (f : ofOver U ⟶ Y) [Etale f]
    (V : smallEtaleSite (ofOver U)) :
    (ofOverFunctor S).map (ofOverPreimage V.hom) ≫ f = ((etaleRestriction f).obj V).hom := sorry

/-- The morphism in `Y_étale` from the postcomposition of `V` with `f` to `f` itself. -/
def etaleLocalizationHom (f : ofOver U ⟶ Y) [Etale f] (V : smallEtaleSite (ofOver U)) :
    (etaleRestriction f).obj V ⟶ smallEtaleSite.mk f :=
  MorphismProperty.CostructuredArrow.homMk (ofOverPreimage V.hom) trivial (by exact etaleLocalizationHom_w f V)

/-- The underlying morphism of schemes over `S` of `etaleLocalizationHom` is `ofOverPreimage`. -/
@[simp]
theorem etaleLocalizationHom_left (f : ofOver U ⟶ Y) [Etale f]
    (V : smallEtaleSite (ofOver U)) :
    (etaleLocalizationHom f V).left = ofOverPreimage V.hom :=
  rfl

/-- Postcomposition with `f` is a morphism over `smallEtaleSite.mk f`. -/
theorem etaleLocalizationHom_naturality (f : ofOver U ⟶ Y) [Etale f]
    {V W : smallEtaleSite (ofOver U)} (g : V ⟶ W) :
    (etaleRestriction f).map g ≫ etaleLocalizationHom f W = etaleLocalizationHom f V :=
  sorry

/-- The site functor `X_étale ⥤ Y_étale / X` for an étale morphism from a scheme. -/
def etaleLocalizationFunctor (f : ofOver U ⟶ Y) [Etale f] :
    smallEtaleSite (ofOver U) ⥤ Over (smallEtaleSite.mk f (hφ := inferInstance)) :=
  (etaleRestriction f).toOver (smallEtaleSite.mk f (hφ := inferInstance)) (etaleLocalizationHom f)
    (etaleLocalizationHom_naturality f)

/-- The object of `X_étale` associated to a slice object over `f`. -/
def etaleLocalizationInverseObj (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (smallEtaleSite.mk f (hφ := inferInstance))) : smallEtaleSite (ofOver U) :=
  @smallEtaleSite.mk S (ofOver U) W.left.left
    (ofOverMap (W.hom.left : W.left.left ⟶ U)) (etale_ofOverMap_of_slice f W)

/-- The underlying map of a slice morphism commutes with its recovered structure maps. -/
private theorem etaleLocalizationInverse_map_w (f : ofOver U ⟶ Y) [Etale f]
    {A B : Over (smallEtaleSite.mk f (hφ := inferInstance))} (g : A ⟶ B) :
    (ofOverFunctor S).map g.left.left ≫ (etaleLocalizationInverseObj f B).hom =
      (etaleLocalizationInverseObj f A).hom := sorry

/-- The recovered map of an identity slice arrow is the identity chart arrow. -/
private theorem etaleLocalizationInverse_map_id (f : ofOver U ⟶ Y) [Etale f]
    (A : Over (smallEtaleSite.mk f (hφ := inferInstance))) :
    (MorphismProperty.CostructuredArrow.homMk (𝟙 A.left.left) trivial
      (etaleLocalizationInverse_map_w f (𝟙 A)) :
        etaleLocalizationInverseObj f A ⟶ etaleLocalizationInverseObj f A) =
      𝟙 (etaleLocalizationInverseObj f A) := sorry

/-- Recovering chart arrows preserves composition of slice arrows. -/
private theorem etaleLocalizationInverse_map_comp (f : ofOver U ⟶ Y) [Etale f]
    {A B C : Over (smallEtaleSite.mk f (hφ := inferInstance))} (g : A ⟶ B) (h : B ⟶ C) :
    (MorphismProperty.CostructuredArrow.homMk (g.left.left ≫ h.left.left) trivial
        (etaleLocalizationInverse_map_w f (g ≫ h)) :
          etaleLocalizationInverseObj f A ⟶ etaleLocalizationInverseObj f C) =
      (MorphismProperty.CostructuredArrow.homMk g.left.left trivial
        (etaleLocalizationInverse_map_w f g) : etaleLocalizationInverseObj f A ⟶
          etaleLocalizationInverseObj f B) ≫
      (MorphismProperty.CostructuredArrow.homMk h.left.left trivial
        (etaleLocalizationInverse_map_w f h) : etaleLocalizationInverseObj f B ⟶
          etaleLocalizationInverseObj f C) := sorry

/-- The inverse site functor `Y_étale / X ⥤ X_étale`, sending a slice object to the
corresponding étale morphism of schemes over `ofOver U`. -/
def etaleLocalizationInverse (f : ofOver U ⟶ Y) [Etale f] :
    Over (smallEtaleSite.mk f (hφ := inferInstance)) ⥤ smallEtaleSite (ofOver U) where
  obj := etaleLocalizationInverseObj f
  map g := MorphismProperty.CostructuredArrow.homMk g.left.left trivial (by exact etaleLocalizationInverse_map_w f g)
  map_id := by intro A; exact etaleLocalizationInverse_map_id f A
  map_comp := by intro A B C g h; exact etaleLocalizationInverse_map_comp f g h

/-- `etaleLocalizationInverseObj` is `smallEtaleSite.mk` of the underlying morphism over
`ofOver U`. -/
@[simp]
theorem etaleLocalizationInverseObj_eq (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (smallEtaleSite.mk f (hφ := inferInstance))) :
    etaleLocalizationInverseObj f W =
      smallEtaleSite.mk (ofOverMap (W.hom.left : W.left.left ⟶ U)) :=
  rfl

/-- On objects, `etaleLocalizationInverse` is `etaleLocalizationInverseObj`. -/
@[simp]
theorem etaleLocalizationInverse_obj (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (smallEtaleSite.mk f (hφ := inferInstance))) :
    (etaleLocalizationInverse f).obj W = etaleLocalizationInverseObj f W :=
  rfl

/-- The underlying scheme over `S` of an inverse-image object is the domain of the slice
object. -/
@[simp]
theorem etaleLocalizationInverse_obj_left (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (smallEtaleSite.mk f (hφ := inferInstance))) :
    ((etaleLocalizationInverse f).obj W).left = W.left.left :=
  rfl

/-- The structure morphism of an inverse-image object is `ofOverMap` of the slice arrow. -/
@[simp]
theorem etaleLocalizationInverse_obj_hom (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (smallEtaleSite.mk f (hφ := inferInstance))) :
    ((etaleLocalizationInverse f).obj W).hom =
      ofOverMap (W.hom.left : W.left.left ⟶ U) :=
  rfl

/-- `etaleLocalizationFunctor` is continuous from `X_étale` to the slice topology on
`Y_étale / X`. -/
instance etaleLocalizationFunctor.instIsContinuous (f : ofOver U ⟶ Y) [Etale f] :
    (etaleLocalizationFunctor f).IsContinuous (smallEtaleTopology (ofOver U))
      ((smallEtaleTopology Y).over (smallEtaleSite.mk f (hφ := inferInstance))) :=
  sorry

/-- `etaleLocalizationFunctor` is cocontinuous from `X_étale` to the slice topology on
`Y_étale / X`. -/
instance etaleLocalizationFunctor.instIsCocontinuous (f : ofOver U ⟶ Y) [Etale f] :
    (etaleLocalizationFunctor f).IsCocontinuous (smallEtaleTopology (ofOver U))
      ((smallEtaleTopology Y).over (smallEtaleSite.mk f (hφ := inferInstance))) :=
  sorry

/-- `etaleLocalizationFunctor` is a morphism of sites from the slice `Y_étale / X` to
`X_étale`. -/
instance etaleLocalizationFunctor.instIsMorphismOfSites (f : ofOver U ⟶ Y) [Etale f] :
    IsMorphismOfSites (smallEtaleTopology (ofOver U))
      ((smallEtaleTopology Y).over (smallEtaleSite.mk f (hφ := inferInstance))) (etaleLocalizationFunctor f) :=
  sorry

/-- `etaleLocalizationInverse` is continuous from the slice `Y_étale / X` to `X_étale`. -/
instance etaleLocalizationInverse.instIsContinuous (f : ofOver U ⟶ Y) [Etale f] :
    (etaleLocalizationInverse f).IsContinuous
      ((smallEtaleTopology Y).over (smallEtaleSite.mk f (hφ := inferInstance))) (smallEtaleTopology (ofOver U)) :=
  sorry

/-- `etaleLocalizationInverse` is cocontinuous from the slice `Y_étale / X` to `X_étale`. -/
instance etaleLocalizationInverse.instIsCocontinuous (f : ofOver U ⟶ Y) [Etale f] :
    (etaleLocalizationInverse f).IsCocontinuous
      ((smallEtaleTopology Y).over (smallEtaleSite.mk f (hφ := inferInstance))) (smallEtaleTopology (ofOver U)) :=
  sorry

/-- `etaleLocalizationInverse` is a morphism of sites from `X_étale` to the slice
`Y_étale / X`. -/
instance etaleLocalizationInverse.instIsMorphismOfSites (f : ofOver U ⟶ Y) [Etale f] :
    IsMorphismOfSites ((smallEtaleTopology Y).over (smallEtaleSite.mk f (hφ := inferInstance)))
      (smallEtaleTopology (ofOver U)) (etaleLocalizationInverse f) :=
  sorry

/-- The site functor `X_étale ⥤ Y_étale / X` is an equivalence of categories. -/
instance etaleLocalizationFunctor.instIsEquivalence (f : ofOver U ⟶ Y) [Etale f] :
    (etaleLocalizationFunctor f).IsEquivalence :=
  sorry

/-- Forgetting the slice recovers étale restriction. -/
def etaleLocalizationFunctor_comp_forget (f : ofOver U ⟶ Y) [Etale f] :
    etaleLocalizationFunctor f ⋙ Over.forget (smallEtaleSite.mk f (hφ := inferInstance)) ≅ etaleRestriction f :=
  (etaleRestriction f).toOverCompForget (smallEtaleSite.mk f (hφ := inferInstance)) (etaleLocalizationHom f)
    (etaleLocalizationHom_naturality f)

/-- Identity section maps commute with restriction along localization arrows. -/
private theorem etaleLocalizationIsoHomStructureSheaf_naturality (f : ofOver U ⟶ Y) [Etale f]
    {A B : (Over (smallEtaleSite.mk f (hφ := inferInstance)))ᵒᵖ} (k : A ⟶ B) :
    ((structureSheaf Y).over (smallEtaleSite.mk f (hφ := inferInstance))).obj.map k ≫ 𝟙 _ =
      𝟙 _ ≫ (((etaleLocalizationInverse f).sheafPushforwardContinuous RingCat.{u}
        ((smallEtaleTopology Y).over (smallEtaleSite.mk f (hφ := inferInstance)))
        (smallEtaleTopology (ofOver U))).obj (structureSheaf (ofOver U))).obj.map k := sorry

/-- Identity-on-sections map from the restricted structure sheaf of `Y` to the pushforward of
`𝒪` along `etaleLocalizationInverse`. -/
def etaleLocalizationIsoHomStructureSheaf (f : ofOver U ⟶ Y) [Etale f] :
    (structureSheaf Y).over (smallEtaleSite.mk f (hφ := inferInstance)) ⟶
      ((etaleLocalizationInverse f).sheafPushforwardContinuous RingCat.{u}
        ((smallEtaleTopology Y).over (smallEtaleSite.mk f (hφ := inferInstance)))
        (smallEtaleTopology (ofOver U))).obj (structureSheaf (ofOver U)) :=
  ⟨{ app := fun _ ↦ 𝟙 _
     naturality := by intro A B k; exact etaleLocalizationIsoHomStructureSheaf_naturality f k }⟩

/-- Identity section maps commute with restriction along localization arrows. -/
private theorem etaleLocalizationIsoInvStructureSheaf_naturality (f : ofOver U ⟶ Y) [Etale f]
    {A B : (smallEtaleSite (ofOver U))ᵒᵖ} (k : A ⟶ B) :
    (structureSheaf (ofOver U)).obj.map k ≫ 𝟙 _ =
      𝟙 _ ≫ (((etaleLocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology (ofOver U))
        ((smallEtaleTopology Y).over (smallEtaleSite.mk f (hφ := inferInstance)))).obj
        ((structureSheaf Y).over (smallEtaleSite.mk f (hφ := inferInstance)))).obj.map k := sorry

/-- Identity-on-sections map from `𝒪` on `X_étale` to the pushforward of the restricted
structure sheaf of `Y` along `etaleLocalizationFunctor`. -/
def etaleLocalizationIsoInvStructureSheaf (f : ofOver U ⟶ Y) [Etale f] :
    structureSheaf (ofOver U) ⟶
      ((etaleLocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology (ofOver U))
        ((smallEtaleTopology Y).over (smallEtaleSite.mk f (hφ := inferInstance)))).obj
        ((structureSheaf Y).over (smallEtaleSite.mk f (hφ := inferInstance))) :=
  ⟨{ app := fun _ ↦ 𝟙 _
     naturality := by intro A B k; exact etaleLocalizationIsoInvStructureSheaf_naturality f k }⟩

/-- The morphism of ringed sites from `(X_étale, 𝒪_X)` to the localization of
`(Y_étale, 𝒪_Y)` at `X`. -/
def etaleLocalizationIsoHom (f : ofOver U ⟶ Y) [Etale f] :
    RingedSiteMap (smallEtaleTopology (ofOver U)) (structureSheaf (ofOver U))
      ((smallEtaleTopology Y).over (smallEtaleSite.mk f (hφ := inferInstance)))
      ((structureSheaf Y).over (smallEtaleSite.mk f (hφ := inferInstance))) where
  base := etaleLocalizationInverse f
  isMorphismOfSites := etaleLocalizationInverse.instIsMorphismOfSites f
  structureSheafMap := etaleLocalizationIsoHomStructureSheaf f

/-- The morphism of ringed sites from the localization of `(Y_étale, 𝒪_Y)` at `X` to
`(X_étale, 𝒪_X)`. -/
def etaleLocalizationIsoInv (f : ofOver U ⟶ Y) [Etale f] :
    RingedSiteMap ((smallEtaleTopology Y).over (smallEtaleSite.mk f (hφ := inferInstance)))
      ((structureSheaf Y).over (smallEtaleSite.mk f (hφ := inferInstance)))
      (smallEtaleTopology (ofOver U)) (structureSheaf (ofOver U)) where
  base := etaleLocalizationFunctor f
  isMorphismOfSites := etaleLocalizationFunctor.instIsMorphismOfSites f
  structureSheafMap := etaleLocalizationIsoInvStructureSheaf f

/-- The forward localization map followed by the inverse is the identity. -/
private theorem etaleLocalizationIso_hom_inv_id (f : ofOver U ⟶ Y) [Etale f] :
    RingedSiteMap.comp (etaleLocalizationIsoHom f) (etaleLocalizationIsoInv f) =
      RingedSiteMap.id (smallEtaleTopology (ofOver U)) (structureSheaf (ofOver U)) := sorry

/-- The inverse localization map followed by the forward map is the identity. -/
private theorem etaleLocalizationIso_inv_hom_id (f : ofOver U ⟶ Y) [Etale f] :
    RingedSiteMap.comp (etaleLocalizationIsoInv f) (etaleLocalizationIsoHom f) =
      RingedSiteMap.id ((smallEtaleTopology Y).over (smallEtaleSite.mk f (hφ := inferInstance)))
        ((structureSheaf Y).over (smallEtaleSite.mk f (hφ := inferInstance))) := sorry

/-- Identification of small étale ringed sites `(X_étale, 𝒪_X) ≅ (Y_étale / X, 𝒪_Y restricted)`
along an étale morphism from a scheme. -/
def etaleLocalizationIso (f : ofOver U ⟶ Y) [Etale f] :
    RingedSiteMap.Iso (smallEtaleTopology (ofOver U)) (structureSheaf (ofOver U))
      ((smallEtaleTopology Y).over (smallEtaleSite.mk f (hφ := inferInstance)))
      ((structureSheaf Y).over (smallEtaleSite.mk f (hφ := inferInstance))) where
  hom := etaleLocalizationIsoHom f
  inv := etaleLocalizationIsoInv f
  hom_inv_id := by exact etaleLocalizationIso_hom_inv_id f
  inv_hom_id := by exact etaleLocalizationIso_inv_hom_id f

/-- The base functor of the forward ringed-site morphism is `etaleLocalizationInverse`. -/
@[simp]
theorem etaleLocalizationIso_hom_base (f : ofOver U ⟶ Y) [Etale f] :
    (etaleLocalizationIso f).hom.base = etaleLocalizationInverse f :=
  rfl

/-- The base functor of the inverse ringed-site morphism is `etaleLocalizationFunctor`. -/
@[simp]
theorem etaleLocalizationIso_inv_base (f : ofOver U ⟶ Y) [Etale f] :
    (etaleLocalizationIso f).inv.base = etaleLocalizationFunctor f :=
  rfl

/-- The forward structure-sheaf comparison is the identity on sections. -/
@[simp]
theorem etaleLocalizationIso_hom_structureSheaf_app (f : ofOver U ⟶ Y) [Etale f]
    (W : (Over (smallEtaleSite.mk f (hφ := inferInstance)))ᵒᵖ) :
    ((etaleLocalizationIso f).hom.structureSheafMap).hom.app W = 𝟙 _ :=
  rfl

/-- The inverse structure-sheaf comparison is the identity on sections. -/
@[simp]
theorem etaleLocalizationIso_inv_structureSheaf_app (f : ofOver U ⟶ Y) [Etale f]
    (V : (smallEtaleSite (ofOver U))ᵒᵖ) :
    ((etaleLocalizationIso f).inv.structureSheafMap).hom.app V = 𝟙 _ :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
