module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import stacks_project.Chap66.«66_27_0_4_Comparison»
public import stacks_project.Chap66.«66_27_0_5_Site»

/-!
# Affine étale localization at an affine scheme

An étale morphism `f : ofOver U ⟶ Y` from an affine scheme to an algebraic space identifies
the affine étale site of `ofOver U` with the localization of the affine étale site of `Y` at
the object `affineEtaleSite.mk f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {Y : AlgebraicSpace S} {U : Over S} [IsAffine U.left]

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
  ObjectProperty.homMk (etaleLocalizationHom f V.obj)

/-- The underlying morphism of schemes over `S` of `affineEtaleLocalizationHom` is
`ofOverPreimage`. -/
@[simp]
theorem affineEtaleLocalizationHom_left (f : ofOver U ⟶ Y) [Etale f]
    (V : affineEtaleSite (ofOver U)) :
    (affineEtaleLocalizationHom f V).hom.left = ofOverPreimage V.obj.hom :=
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
    ObjectProperty.homMk (MorphismProperty.CostructuredArrow.homMk g.left.hom.left trivial sorry)
  map_id := sorry
  map_comp := sorry

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
  sorry

/-- The unit component identifying an affine étale object with its image under localization
followed by the inverse. -/
def affineEtaleLocalizationUnitApp (f : ofOver U ⟶ Y) [Etale f]
    (V : affineEtaleSite (ofOver U)) :
    V ≅ (affineEtaleLocalizationInverse f).obj ((affineEtaleLocalizationFunctor f).obj V) where
  hom := ObjectProperty.homMk (MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial sorry)
  inv := ObjectProperty.homMk (MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial sorry)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The counit component identifying the localization of an inverse-image object with the original
slice object. -/
def affineEtaleLocalizationCounitApp (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (affineEtaleSite.mk f)) :
    (affineEtaleLocalizationFunctor f).obj ((affineEtaleLocalizationInverse f).obj W) ≅ W where
  hom := Over.homMk
    (ObjectProperty.homMk (MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial sorry)) sorry
  inv := Over.homMk
    (ObjectProperty.homMk (MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial sorry)) sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

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
