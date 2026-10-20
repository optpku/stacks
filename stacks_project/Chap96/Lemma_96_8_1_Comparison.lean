/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.RingedSite.Topos
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.AlgebraicGeometry.GroupoidsOver.RepresentableRingedSite
public import stacks_project.Chap96.Lemma_96_8_1_RingedSite

/-!
# Comparison of associated ringed sites with big scheme sites

A representing equivalence `𝒳 ≌ slice X` and the iterated-slice identification
`Over X ≃ Over X.left` induce a canonical morphism of ringed sites
`(𝒳_τ, 𝒪_𝒳) ⟶ ((Sch/X.left)_τ, 𝒪)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The structure-sheaf map of `associatedRingedSiteEquivHom`, identifying
`𝒪_{slice X}` with the continuous pushforward of `𝒪_𝒳` along
`toFunctor e.inv`. -/
def associatedRingedSiteEquivHom_structureSheafMap
    {𝒳 : GroupoidsOver S} {X : Over S} (e : 𝒳 ≌ slice X)
    (τ : StandardTopology) :
    (associatedRingedSite (slice X) τ).structureSheaf ⟶
      ((toFunctor e.inv).sheafPushforwardContinuous RingCat.{u}
        ((slice X).associatedTopology τ) (𝒳.associatedTopology τ)).obj
        (associatedRingedSite 𝒳 τ).structureSheaf :=
  associatedRingedSiteEquivMap_structureSheafMap e τ

/-- The morphism of associated `τ`-ringed sites induced by a representing
equivalence `e : 𝒳 ≌ slice X`, with underlying functor `toFunctor e.inv`. -/
def associatedRingedSiteEquivHom {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    RingedSite.Hom (associatedRingedSite 𝒳 τ)
      (associatedRingedSite (slice X) τ) where
  base := (associatedRingedSiteEquivMap e τ).base
  isMorphismOfSites := (associatedRingedSiteEquivMap e τ).isMorphismOfSites
  structureSheafMap := (associatedRingedSiteEquivMap e τ).structureSheafMap

/-- The base of `associatedRingedSiteEquivHom e τ` is `toFunctor e.inv`. -/
theorem associatedRingedSiteEquivHom_base {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    (associatedRingedSiteEquivHom e τ).base = toFunctor e.inv :=
  rfl

/-- The structure-sheaf map of `sliceAssociatedRingedSiteHom`, given by the
identity realization triangle
`iteratedSliceBackward ⋙ (slice X).p ⋙ Over.forget S = Over.forget X.left`. -/
def sliceAssociatedRingedSiteHom_structureSheafMap (X : Over S)
    (τ : StandardTopology) :
    (StandardTopology.Big.ringedSite τ X.left).structureSheaf ⟶
      (X.iteratedSliceBackward.sheafPushforwardContinuous RingCat.{u}
        (τ.overTopology X.left) ((slice X).associatedTopology τ)).obj
        (associatedRingedSite (slice X) τ).structureSheaf :=
  sliceAssociatedRingedSiteMap_structureSheafMap X τ

/-- The canonical morphism of ringed sites from the associated `τ`-site of
`slice X` to the big `τ`-site of the scheme `X.left`. -/
def sliceAssociatedRingedSiteHom (X : Over S) (τ : StandardTopology) :
    RingedSite.Hom (associatedRingedSite (slice X) τ)
      (StandardTopology.Big.ringedSite τ X.left) where
  base := (sliceAssociatedRingedSiteMap X τ).base
  isMorphismOfSites := (sliceAssociatedRingedSiteMap X τ).isMorphismOfSites
  structureSheafMap := (sliceAssociatedRingedSiteMap X τ).structureSheafMap

/-- The base of `sliceAssociatedRingedSiteHom X τ` is `X.iteratedSliceBackward`. -/
theorem sliceAssociatedRingedSiteHom_base (X : Over S) (τ : StandardTopology) :
    (sliceAssociatedRingedSiteHom X τ).base = X.iteratedSliceBackward :=
  rfl

/-- The canonical morphism of ringed sites `(𝒳_τ, 𝒪_𝒳) ⟶ ((Sch/X.left)_τ, 𝒪)`
induced by a representing equivalence `e : 𝒳 ≌ slice X`. -/
def associatedRingedSiteHom {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    RingedSite.Hom (associatedRingedSite 𝒳 τ)
      (StandardTopology.Big.ringedSite τ X.left) where
  base := (associatedRingedSiteMap e τ).base
  isMorphismOfSites := (associatedRingedSiteMap e τ).isMorphismOfSites
  structureSheafMap := (associatedRingedSiteMap e τ).structureSheafMap

/-- The base of `associatedRingedSiteHom e τ` is the composite
`X.iteratedSliceBackward ⋙ toFunctor e.inv`. -/
theorem associatedRingedSiteHom_base {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    (associatedRingedSiteHom e τ).base =
      X.iteratedSliceBackward ⋙ toFunctor e.inv :=
  rfl

/-- `associatedRingedSiteHom e τ` is the composite of the representing
equivalence comparison with the iterated-slice comparison. -/
theorem associatedRingedSiteHom_eq {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    associatedRingedSiteHom e τ =
      RingedSite.Hom.comp (associatedRingedSiteEquivHom e τ)
        (sliceAssociatedRingedSiteHom X τ) :=
  rfl

/-- Objectwise, the structure-sheaf map of `sliceAssociatedRingedSiteHom`
is pullback of global sections along the identity of the underlying scheme. -/
theorem sliceAssociatedRingedSiteHom_structureSheafMap_app (X : Over S)
    (τ : StandardTopology) (U : (Over X.left)ᵒᵖ) :
    (sliceAssociatedRingedSiteHom X τ).structureSheafMap.hom.app U =
      RingCat.ofHom
        (𝟙 U.unop.left : U.unop.left ⟶ U.unop.left).appTop.hom :=
  rfl

end AlgebraicGeometry.GroupoidsOver
