/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_18_12_Restriction

/-!
# Étale localization of small étale ringed sites at a scheme

An étale morphism `f : ofOver U ⟶ Y` from a scheme to an algebraic space identifies the
small étale ringed site of `ofOver U` with the localization of the small étale ringed site of
`Y` at the object `smallEtaleSite.mk f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The morphism in `Over S` recovered from a morphism of algebraic spaces between schemes
over `S`. -/
def ofOverPreimage {U V : Over S} (φ : ofOver U ⟶ ofOver V) : U ⟶ V :=
  Yoneda.fullyFaithful.preimage (φ : yoneda.obj U ⟶ yoneda.obj V)

/-- `ofOverMap` inverts `ofOverPreimage`. -/
theorem ofOverMap_preimage {U V : Over S} (φ : ofOver U ⟶ ofOver V) :
    ofOverMap (ofOverPreimage φ) = φ :=
  sorry

/-- `ofOverPreimage` inverts `ofOverMap`. -/
theorem ofOverPreimage_map {U V : Over S} (g : U ⟶ V) :
    ofOverPreimage (ofOverMap g) = g :=
  sorry

variable {Y : AlgebraicSpace S} {U : Over S}

/-- A morphism in the slice `Y_étale / f` remains étale over the scheme `ofOver U`. -/
instance etale_ofOverMap_of_slice (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (smallEtaleSite.mk f)) :
    Etale (ofOverMap (W.hom.left : W.left.left ⟶ U)) :=
  sorry

/-- The morphism in `Y_étale` from the postcomposition of `V` with `f` to `f` itself. -/
def etaleLocalizationHom (f : ofOver U ⟶ Y) [Etale f] (V : smallEtaleSite (ofOver U)) :
    (etaleRestriction f).obj V ⟶ smallEtaleSite.mk f :=
  MorphismProperty.CostructuredArrow.homMk (ofOverPreimage V.hom) trivial sorry

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
    smallEtaleSite (ofOver U) ⥤ Over (smallEtaleSite.mk f) :=
  (etaleRestriction f).toOver (smallEtaleSite.mk f) (etaleLocalizationHom f)
    (etaleLocalizationHom_naturality f)

/-- The object of `X_étale` associated to a slice object over `f`. -/
def etaleLocalizationInverseObj (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (smallEtaleSite.mk f)) : smallEtaleSite (ofOver U) :=
  @smallEtaleSite.mk S (ofOver U) W.left.left
    (ofOverMap (W.hom.left : W.left.left ⟶ U)) (etale_ofOverMap_of_slice f W)

/-- The inverse site functor `Y_étale / X ⥤ X_étale`, sending a slice object to the
corresponding étale morphism of schemes over `ofOver U`. -/
def etaleLocalizationInverse (f : ofOver U ⟶ Y) [Etale f] :
    Over (smallEtaleSite.mk f) ⥤ smallEtaleSite (ofOver U) where
  obj := etaleLocalizationInverseObj f
  map g := MorphismProperty.CostructuredArrow.homMk g.left.left trivial sorry
  map_id := sorry
  map_comp := sorry

/-- `etaleLocalizationInverseObj` is `smallEtaleSite.mk` of the underlying morphism over
`ofOver U`. -/
@[simp]
theorem etaleLocalizationInverseObj_eq (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (smallEtaleSite.mk f)) :
    etaleLocalizationInverseObj f W =
      smallEtaleSite.mk (ofOverMap (W.hom.left : W.left.left ⟶ U)) :=
  rfl

/-- On objects, `etaleLocalizationInverse` is `etaleLocalizationInverseObj`. -/
@[simp]
theorem etaleLocalizationInverse_obj (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (smallEtaleSite.mk f)) :
    (etaleLocalizationInverse f).obj W = etaleLocalizationInverseObj f W :=
  rfl

/-- The underlying scheme over `S` of an inverse-image object is the domain of the slice
object. -/
@[simp]
theorem etaleLocalizationInverse_obj_left (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (smallEtaleSite.mk f)) :
    ((etaleLocalizationInverse f).obj W).left = W.left.left :=
  rfl

/-- The structure morphism of an inverse-image object is `ofOverMap` of the slice arrow. -/
@[simp]
theorem etaleLocalizationInverse_obj_hom (f : ofOver U ⟶ Y) [Etale f]
    (W : Over (smallEtaleSite.mk f)) :
    ((etaleLocalizationInverse f).obj W).hom =
      ofOverMap (W.hom.left : W.left.left ⟶ U) :=
  rfl

/-- `etaleLocalizationFunctor` is continuous from `X_étale` to the slice topology on
`Y_étale / X`. -/
instance etaleLocalizationFunctor.instIsContinuous (f : ofOver U ⟶ Y) [Etale f] :
    (etaleLocalizationFunctor f).IsContinuous (smallEtaleTopology (ofOver U))
      ((smallEtaleTopology Y).over (smallEtaleSite.mk f)) :=
  sorry

/-- `etaleLocalizationFunctor` is cocontinuous from `X_étale` to the slice topology on
`Y_étale / X`. -/
instance etaleLocalizationFunctor.instIsCocontinuous (f : ofOver U ⟶ Y) [Etale f] :
    (etaleLocalizationFunctor f).IsCocontinuous (smallEtaleTopology (ofOver U))
      ((smallEtaleTopology Y).over (smallEtaleSite.mk f)) :=
  sorry

/-- `etaleLocalizationFunctor` is a morphism of sites from the slice `Y_étale / X` to
`X_étale`. -/
instance etaleLocalizationFunctor.instIsMorphismOfSites (f : ofOver U ⟶ Y) [Etale f] :
    IsMorphismOfSites (smallEtaleTopology (ofOver U))
      ((smallEtaleTopology Y).over (smallEtaleSite.mk f)) (etaleLocalizationFunctor f) :=
  sorry

/-- `etaleLocalizationInverse` is continuous from the slice `Y_étale / X` to `X_étale`. -/
instance etaleLocalizationInverse.instIsContinuous (f : ofOver U ⟶ Y) [Etale f] :
    (etaleLocalizationInverse f).IsContinuous
      ((smallEtaleTopology Y).over (smallEtaleSite.mk f)) (smallEtaleTopology (ofOver U)) :=
  sorry

/-- `etaleLocalizationInverse` is cocontinuous from the slice `Y_étale / X` to `X_étale`. -/
instance etaleLocalizationInverse.instIsCocontinuous (f : ofOver U ⟶ Y) [Etale f] :
    (etaleLocalizationInverse f).IsCocontinuous
      ((smallEtaleTopology Y).over (smallEtaleSite.mk f)) (smallEtaleTopology (ofOver U)) :=
  sorry

/-- `etaleLocalizationInverse` is a morphism of sites from `X_étale` to the slice
`Y_étale / X`. -/
instance etaleLocalizationInverse.instIsMorphismOfSites (f : ofOver U ⟶ Y) [Etale f] :
    IsMorphismOfSites ((smallEtaleTopology Y).over (smallEtaleSite.mk f))
      (smallEtaleTopology (ofOver U)) (etaleLocalizationInverse f) :=
  sorry

/-- The site functor `X_étale ⥤ Y_étale / X` is an equivalence of categories. -/
instance etaleLocalizationFunctor.instIsEquivalence (f : ofOver U ⟶ Y) [Etale f] :
    (etaleLocalizationFunctor f).IsEquivalence :=
  sorry

/-- Forgetting the slice recovers étale restriction. -/
def etaleLocalizationFunctor_comp_forget (f : ofOver U ⟶ Y) [Etale f] :
    etaleLocalizationFunctor f ⋙ Over.forget (smallEtaleSite.mk f) ≅ etaleRestriction f :=
  (etaleRestriction f).toOverCompForget (smallEtaleSite.mk f) (etaleLocalizationHom f)
    (etaleLocalizationHom_naturality f)

/-- Identity-on-sections map from the restricted structure sheaf of `Y` to the pushforward of
`𝒪` along `etaleLocalizationInverse`. -/
def etaleLocalizationIsoHomStructureSheaf (f : ofOver U ⟶ Y) [Etale f] :
    (structureSheaf Y).over (smallEtaleSite.mk f) ⟶
      ((etaleLocalizationInverse f).sheafPushforwardContinuous RingCat.{u}
        ((smallEtaleTopology Y).over (smallEtaleSite.mk f))
        (smallEtaleTopology (ofOver U))).obj (structureSheaf (ofOver U)) :=
  ⟨{ app := fun _ ↦ 𝟙 _
     naturality := sorry }⟩

/-- Identity-on-sections map from `𝒪` on `X_étale` to the pushforward of the restricted
structure sheaf of `Y` along `etaleLocalizationFunctor`. -/
def etaleLocalizationIsoInvStructureSheaf (f : ofOver U ⟶ Y) [Etale f] :
    structureSheaf (ofOver U) ⟶
      ((etaleLocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
        (smallEtaleTopology (ofOver U))
        ((smallEtaleTopology Y).over (smallEtaleSite.mk f))).obj
        ((structureSheaf Y).over (smallEtaleSite.mk f)) :=
  ⟨{ app := fun _ ↦ 𝟙 _
     naturality := sorry }⟩

/-- The morphism of ringed sites from `(X_étale, 𝒪_X)` to the localization of
`(Y_étale, 𝒪_Y)` at `X`. -/
def etaleLocalizationIsoHom (f : ofOver U ⟶ Y) [Etale f] :
    RingedSite.Hom (ringedSite (ofOver U))
      ((ringedSite Y).localization (smallEtaleSite.mk f)) where
  base := etaleLocalizationInverse f
  structureSheafMap := etaleLocalizationIsoHomStructureSheaf f

/-- The morphism of ringed sites from the localization of `(Y_étale, 𝒪_Y)` at `X` to
`(X_étale, 𝒪_X)`. -/
def etaleLocalizationIsoInv (f : ofOver U ⟶ Y) [Etale f] :
    RingedSite.Hom ((ringedSite Y).localization (smallEtaleSite.mk f))
      (ringedSite (ofOver U)) where
  base := etaleLocalizationFunctor f
  structureSheafMap := etaleLocalizationIsoInvStructureSheaf f

/-- Identification of small étale ringed sites `(X_étale, 𝒪_X) ≅ (Y_étale / X, 𝒪_Y restricted)`
along an étale morphism from a scheme. -/
def etaleLocalizationIso (f : ofOver U ⟶ Y) [Etale f] :
    ringedSite (ofOver U) ≅ (ringedSite Y).localization (smallEtaleSite.mk f) where
  hom := etaleLocalizationIsoHom f
  inv := etaleLocalizationIsoInv f
  hom_inv_id := sorry
  inv_hom_id := sorry

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
    (W : (Over (smallEtaleSite.mk f))ᵒᵖ) :
    ((etaleLocalizationIso f).hom.structureSheafMap).hom.app W = 𝟙 _ :=
  rfl

/-- The inverse structure-sheaf comparison is the identity on sections. -/
@[simp]
theorem etaleLocalizationIso_inv_structureSheaf_app (f : ofOver U ⟶ Y) [Etale f]
    (V : (smallEtaleSite (ofOver U))ᵒᵖ) :
    ((etaleLocalizationIso f).inv.structureSheafMap).hom.app V = 𝟙 _ :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
