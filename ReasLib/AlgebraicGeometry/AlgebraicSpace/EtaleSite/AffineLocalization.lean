/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationRestriction
public import ReasLib.CategoryTheory.Sites.MorphismOfSites

/-!
# Affine étale localization

Postcomposition along an étale morphism acts on affine étale sites. For an
étale morphism from an affine scheme, this identifies its affine étale site
with the slice site over the corresponding affine chart.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Postcomposition with an étale morphism `f : X ⟶ Y` sends affine schemes étale over `X`
to affine schemes étale over `Y`. -/
def affineEtaleRestriction {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    affineEtaleSite X ⥤ affineEtaleSite Y where
  obj U :=
    { obj := (etaleRestriction f).obj U.obj
      property := U.property }
  map g := ObjectProperty.homMk ((etaleRestriction f).map g.hom)
  map_id U := ObjectProperty.hom_ext _ ((etaleRestriction f).map_id U.obj)
  map_comp g h := ObjectProperty.hom_ext _ ((etaleRestriction f).map_comp g.hom h.hom)

/-- The object map of `affineEtaleRestriction f` is `etaleRestriction f` on the underlying
small étale object. -/
@[simp]
theorem affineEtaleRestriction_obj {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (U : affineEtaleSite X) :
    ((affineEtaleRestriction f).obj U).obj = (etaleRestriction f).obj U.obj :=
  rfl

/-- The morphism map of `affineEtaleRestriction f` is `etaleRestriction f` on the underlying
small étale morphism. -/
@[simp]
theorem affineEtaleRestriction_map {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    {U V : affineEtaleSite X} (g : U ⟶ V) :
    ((affineEtaleRestriction f).map g).hom = (etaleRestriction f).map g.hom :=
  rfl

/-- Postcomposition on affine étale sites preserves the underlying scheme over `S`. -/
@[simp]
theorem affineEtaleRestriction_obj_left {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (U : affineEtaleSite X) :
    ((affineEtaleRestriction f).obj U).obj.left = U.obj.left :=
  rfl

/-- Postcomposition with an étale morphism is continuous for the affine étale topologies. -/
instance affineEtaleRestriction.instIsContinuous {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    (affineEtaleRestriction f).IsContinuous (affineEtaleTopology X) (affineEtaleTopology Y) :=
  sorry

/-- Postcomposition with an étale morphism is cocontinuous for the affine étale topologies. -/
instance affineEtaleRestriction.instIsCocontinuous {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] :
    (affineEtaleRestriction f).IsCocontinuous (affineEtaleTopology X) (affineEtaleTopology Y) :=
  sorry

variable {Y : AlgebraicSpace S} {U : Over S} [IsAffine U.left]

/-- A morphism in the slice `Y_{affine,étale} / f` remains étale over the affine scheme
`ofOver U`. -/
instance etale_ofOverMap_of_affineSlice (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (affineEtaleSite.mk f)) :
    Etale (ofOverMap (W.hom.hom.left : W.left.obj.left ⟶ U)) :=
  sorry

/-- The morphism in `Y_{affine,étale}` from the postcomposition of `V` with `f` to `f` itself. -/
def affineEtaleLocalizationHom (f : ofOver U ⟶ Y) [Etale f]
    (V : affineEtaleSite (ofOver U)) :
    (affineEtaleRestriction f).obj V ⟶ affineEtaleSite.mk f :=
  ObjectProperty.homMk (MorphismProperty.CostructuredArrow.homMk
    (Yoneda.fullyFaithful.preimage (V.obj.hom : yoneda.obj V.obj.left ⟶ yoneda.obj U))
    trivial (by
      change yoneda.map (Yoneda.fullyFaithful.preimage _) ≫ f = V.obj.hom ≫ f
      rw [Yoneda.fullyFaithful.map_preimage]
      rfl))

/-- The underlying morphism of schemes over `S` of `affineEtaleLocalizationHom` is
the canonical Yoneda preimage of its structure morphism. -/
@[simp]
theorem affineEtaleLocalizationHom_left (f : ofOver U ⟶ Y) [Etale f]
    (V : affineEtaleSite (ofOver U)) :
    (affineEtaleLocalizationHom f V).hom.left =
      Yoneda.fullyFaithful.preimage (V.obj.hom : yoneda.obj V.obj.left ⟶ yoneda.obj U) :=
  rfl

/-- Postcomposition with `f` is a morphism over `affineEtaleSite.mk f`. -/
theorem affineEtaleLocalizationHom_naturality (f : ofOver U ⟶ Y) [Etale f]
    {V W : affineEtaleSite (ofOver U)} (g : V ⟶ W) :
    (affineEtaleRestriction f).map g ≫ affineEtaleLocalizationHom f W =
      affineEtaleLocalizationHom f V :=
  sorry

/-- The site functor `X_{affine,étale} ⥤ Y_{affine,étale} / X` for an étale morphism from an
affine scheme. -/
def affineEtaleLocalizationFunctor (f : ofOver U ⟶ Y) [Etale f] :
    affineEtaleSite (ofOver U) ⥤ Over (affineEtaleSite.mk f) :=
  (affineEtaleRestriction f).toOver (affineEtaleSite.mk f) (affineEtaleLocalizationHom f)
    (affineEtaleLocalizationHom_naturality f)

/-- The object of `X_{affine,étale}` associated to a slice object over `f`. -/
def affineEtaleLocalizationInverseObj (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (affineEtaleSite.mk f)) : affineEtaleSite (ofOver U) :=
  @affineEtaleSite.mk S (ofOver U) W.left.obj.left (affineEtaleSite_obj_isAffine W.left)
    (ofOverMap (W.hom.hom.left : W.left.obj.left ⟶ U)) (etale_ofOverMap_of_affineSlice f W)

/-- The inverse site functor `Y_{affine,étale} / X ⥤ X_{affine,étale}`, sending a slice object
to the corresponding étale morphism of affine schemes over `ofOver U`. -/
def affineEtaleLocalizationInverse (f : ofOver U ⟶ Y) [Etale f] :
    Over (affineEtaleSite.mk f) ⥤ affineEtaleSite (ofOver U) where
  obj := affineEtaleLocalizationInverseObj f
  map g :=
    ObjectProperty.homMk (MorphismProperty.CostructuredArrow.homMk g.left.hom.left trivial (by
      change yoneda.map g.left.hom.left ≫ yoneda.map _ = yoneda.map _
      rw [← yoneda.map_comp]
      exact congrArg yoneda.map (congrArg (fun h => h.hom.left) g.w)))
  map_id W := by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.CostructuredArrow.Hom.ext
    rfl
  map_comp g h := by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.CostructuredArrow.Hom.ext
    rfl

/-- `affineEtaleLocalizationInverseObj` is `affineEtaleSite.mk` of the underlying morphism over
`ofOver U`. -/
@[simp]
theorem affineEtaleLocalizationInverseObj_eq (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (affineEtaleSite.mk f)) :
    affineEtaleLocalizationInverseObj f W =
      @affineEtaleSite.mk S (ofOver U) W.left.obj.left (affineEtaleSite_obj_isAffine W.left)
        (ofOverMap (W.hom.hom.left : W.left.obj.left ⟶ U)) (etale_ofOverMap_of_affineSlice f W) :=
  rfl

/-- On objects, `affineEtaleLocalizationInverse` is `affineEtaleLocalizationInverseObj`. -/
@[simp]
theorem affineEtaleLocalizationInverse_obj (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (affineEtaleSite.mk f)) :
    (affineEtaleLocalizationInverse f).obj W = affineEtaleLocalizationInverseObj f W :=
  rfl

/-- The underlying scheme over `S` of an inverse-image object is the domain of the slice object. -/
@[simp]
theorem affineEtaleLocalizationInverse_obj_left (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (affineEtaleSite.mk f)) :
    ((affineEtaleLocalizationInverse f).obj W).obj.left = W.left.obj.left :=
  rfl

/-- The structure morphism of an inverse-image object is `ofOverMap` of the slice arrow. -/
theorem affineEtaleLocalizationInverse_obj_hom (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (affineEtaleSite.mk f)) :
    ((affineEtaleLocalizationInverse f).obj W).obj.hom =
      ofOverMap (W.hom.hom.left : W.left.obj.left ⟶ U) :=
  rfl

/-- The unit component identifying an affine étale object with its image under localization
followed by the inverse. -/
def affineEtaleLocalizationUnitApp (f : ofOver U ⟶ Y) [Etale f]
    (V : affineEtaleSite (ofOver U)) :
    V ≅ (affineEtaleLocalizationInverse f).obj ((affineEtaleLocalizationFunctor f).obj V) where
  hom := ObjectProperty.homMk (MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial (by
    change yoneda.map (𝟙 _) ≫ yoneda.map (Yoneda.fullyFaithful.preimage _) = V.obj.hom
    rw [yoneda.map_id, Category.id_comp, Yoneda.fullyFaithful.map_preimage]))
  inv := ObjectProperty.homMk (MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial (by
    change yoneda.map (𝟙 _) ≫ V.obj.hom = yoneda.map (Yoneda.fullyFaithful.preimage _)
    rw [yoneda.map_id, Category.id_comp, Yoneda.fullyFaithful.map_preimage]))
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.CostructuredArrow.Hom.ext
    exact Category.id_comp _
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.CostructuredArrow.Hom.ext
    exact Category.id_comp _

/-- The counit component identifying the localization of an inverse-image object with the original
slice object. -/
def affineEtaleLocalizationCounitApp (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (affineEtaleSite.mk f)) :
    (affineEtaleLocalizationFunctor f).obj ((affineEtaleLocalizationInverse f).obj W) ≅ W where
  hom := Over.homMk
    (ObjectProperty.homMk (MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial (by
      change yoneda.map (𝟙 _) ≫ W.left.obj.hom = yoneda.map W.hom.hom.left ≫ f
      rw [yoneda.map_id, Category.id_comp]
      exact W.hom.hom.w.symm))) (by
        apply ObjectProperty.hom_ext
        apply MorphismProperty.CostructuredArrow.Hom.ext
        change 𝟙 _ ≫ W.hom.hom.left = Yoneda.fullyFaithful.preimage (yoneda.map _)
        rw [Category.id_comp, Yoneda.fullyFaithful.preimage_map])
  inv := Over.homMk
    (ObjectProperty.homMk (MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial (by
      change yoneda.map (𝟙 _) ≫ (yoneda.map W.hom.hom.left ≫ f) = W.left.obj.hom
      rw [yoneda.map_id, Category.id_comp]
      exact W.hom.hom.w))) (by
        apply ObjectProperty.hom_ext
        apply MorphismProperty.CostructuredArrow.Hom.ext
        change 𝟙 _ ≫ Yoneda.fullyFaithful.preimage (yoneda.map _) = W.hom.hom.left
        rw [Category.id_comp, Yoneda.fullyFaithful.preimage_map])
  hom_inv_id := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply MorphismProperty.CostructuredArrow.Hom.ext
    exact Category.id_comp _
  inv_hom_id := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply MorphismProperty.CostructuredArrow.Hom.ext
    exact Category.id_comp _

/-- The unit isomorphism of affine étale localization. -/
def affineEtaleLocalizationUnitIso (f : ofOver U ⟶ Y) [Etale f] :
    𝟭 (affineEtaleSite (ofOver U)) ≅
      affineEtaleLocalizationFunctor f ⋙ affineEtaleLocalizationInverse f :=
  NatIso.ofComponents (affineEtaleLocalizationUnitApp f) sorry

/-- The counit isomorphism of affine étale localization. -/
def affineEtaleLocalizationCounitIso (f : ofOver U ⟶ Y) [Etale f] :
    affineEtaleLocalizationInverse f ⋙ affineEtaleLocalizationFunctor f ≅
      𝟭 (Over (affineEtaleSite.mk f)) :=
  NatIso.ofComponents (affineEtaleLocalizationCounitApp f) sorry

/-- Identification of affine étale sites `X_{affine,étale} ≌ Y_{affine,étale} / X` along an étale
morphism from an affine scheme. -/
def affineEtaleLocalizationEquiv (f : ofOver U ⟶ Y) [Etale f] :
    affineEtaleSite (ofOver U) ≌ Over (affineEtaleSite.mk f) :=
  CategoryTheory.Equivalence.mk (affineEtaleLocalizationFunctor f)
    (affineEtaleLocalizationInverse f) (affineEtaleLocalizationUnitIso f)
    (affineEtaleLocalizationCounitIso f)

/-- The forward functor of `affineEtaleLocalizationEquiv` is `affineEtaleLocalizationFunctor`. -/
@[simp]
theorem affineEtaleLocalizationEquiv_functor (f : ofOver U ⟶ Y) [Etale f] :
    (affineEtaleLocalizationEquiv f).functor = affineEtaleLocalizationFunctor f :=
  rfl

/-- The inverse functor of `affineEtaleLocalizationEquiv` is `affineEtaleLocalizationInverse`. -/
@[simp]
theorem affineEtaleLocalizationEquiv_inverse (f : ofOver U ⟶ Y) [Etale f] :
    (affineEtaleLocalizationEquiv f).inverse = affineEtaleLocalizationInverse f :=
  rfl

/-- `affineEtaleLocalizationFunctor` is continuous from `X_{affine,étale}` to the slice topology
on `Y_{affine,étale} / X`. -/
instance affineEtaleLocalizationFunctor.instIsContinuous (f : ofOver U ⟶ Y) [Etale f] :
    (affineEtaleLocalizationFunctor f).IsContinuous (affineEtaleTopology (ofOver U))
      ((affineEtaleTopology Y).over (affineEtaleSite.mk f)) :=
  sorry

/-- `affineEtaleLocalizationFunctor` is cocontinuous from `X_{affine,étale}` to the slice topology
on `Y_{affine,étale} / X`. -/
instance affineEtaleLocalizationFunctor.instIsCocontinuous (f : ofOver U ⟶ Y) [Etale f] :
    (affineEtaleLocalizationFunctor f).IsCocontinuous (affineEtaleTopology (ofOver U))
      ((affineEtaleTopology Y).over (affineEtaleSite.mk f)) :=
  sorry

/-- `affineEtaleLocalizationFunctor` is a morphism of sites from the slice
`Y_{affine,étale} / X` to `X_{affine,étale}`. -/
instance affineEtaleLocalizationFunctor.instIsMorphismOfSites (f : ofOver U ⟶ Y) [Etale f] :
    IsMorphismOfSites (affineEtaleTopology (ofOver U))
      ((affineEtaleTopology Y).over (affineEtaleSite.mk f)) (affineEtaleLocalizationFunctor f) :=
  sorry

/-- `affineEtaleLocalizationInverse` is continuous from the slice `Y_{affine,étale} / X` to
`X_{affine,étale}`. -/
instance affineEtaleLocalizationInverse.instIsContinuous (f : ofOver U ⟶ Y) [Etale f] :
    (affineEtaleLocalizationInverse f).IsContinuous
      ((affineEtaleTopology Y).over (affineEtaleSite.mk f)) (affineEtaleTopology (ofOver U)) :=
  sorry

/-- `affineEtaleLocalizationInverse` is cocontinuous from the slice `Y_{affine,étale} / X` to
`X_{affine,étale}`. -/
instance affineEtaleLocalizationInverse.instIsCocontinuous (f : ofOver U ⟶ Y) [Etale f] :
    (affineEtaleLocalizationInverse f).IsCocontinuous
      ((affineEtaleTopology Y).over (affineEtaleSite.mk f)) (affineEtaleTopology (ofOver U)) :=
  sorry

/-- `affineEtaleLocalizationInverse` is a morphism of sites from `X_{affine,étale}` to the slice
`Y_{affine,étale} / X`. -/
instance affineEtaleLocalizationInverse.instIsMorphismOfSites (f : ofOver U ⟶ Y) [Etale f] :
    IsMorphismOfSites ((affineEtaleTopology Y).over (affineEtaleSite.mk f))
      (affineEtaleTopology (ofOver U)) (affineEtaleLocalizationInverse f) :=
  sorry

/-- The site functor `X_{affine,étale} ⥤ Y_{affine,étale} / X` is an equivalence of categories. -/
instance affineEtaleLocalizationFunctor.instIsEquivalence (f : ofOver U ⟶ Y) [Etale f] :
    (affineEtaleLocalizationFunctor f).IsEquivalence :=
  Functor.IsEquivalence.mk' (affineEtaleLocalizationInverse f)
    (affineEtaleLocalizationUnitIso f) (affineEtaleLocalizationCounitIso f)

/-- The inverse site functor `Y_{affine,étale} / X ⥤ X_{affine,étale}` is an equivalence of
categories. -/
instance affineEtaleLocalizationInverse.instIsEquivalence (f : ofOver U ⟶ Y) [Etale f] :
    (affineEtaleLocalizationInverse f).IsEquivalence :=
  Functor.IsEquivalence.mk' (affineEtaleLocalizationFunctor f)
    (affineEtaleLocalizationCounitIso f).symm (affineEtaleLocalizationUnitIso f).symm

/-- Forgetting the slice recovers affine étale restriction. -/
def affineEtaleLocalizationFunctor_comp_forget (f : ofOver U ⟶ Y) [Etale f] :
    affineEtaleLocalizationFunctor f ⋙ Over.forget (affineEtaleSite.mk f) ≅
      affineEtaleRestriction f :=
  (affineEtaleRestriction f).toOverCompForget (affineEtaleSite.mk f)
    (affineEtaleLocalizationHom f) (affineEtaleLocalizationHom_naturality f)

end AlgebraicGeometry.AlgebraicSpace
