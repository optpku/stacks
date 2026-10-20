/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Sites.Ringed.Equivalence
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.AlgebraicGeometry.GroupoidsOver.AssociatedStructureSheaf

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

/-- The inverse of a representing equivalence `e : 𝒳 ≌ slice X` is a morphism of
associated `τ`-sites: `toFunctor e.inv` is an equivalence, hence representably
flat, and cartesian functors are continuous for inherited topologies. -/
instance toFunctor_inv_isMorphismOfSites {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    IsMorphismOfSites ((slice X).associatedTopology τ) (𝒳.associatedTopology τ)
      (toFunctor e.inv) :=
  sorry

/-- The iterated-slice functor `Over X.left ⥤ Over X` is a morphism of sites
from `(Sch/X.left)_τ` to the associated `τ`-site of `slice X`. -/
instance iteratedSliceBackward_isMorphismOfSites (X : Over S)
    (τ : StandardTopology) :
    IsMorphismOfSites (τ.overTopology X.left) ((slice X).associatedTopology τ)
      X.iteratedSliceBackward :=
  sorry

/-- The iterated-slice functor is continuous for the associated `τ`-topologies. -/
instance iteratedSliceBackward_isContinuous (X : Over S)
    (τ : StandardTopology) :
    X.iteratedSliceBackward.IsContinuous (τ.overTopology X.left)
      ((slice X).associatedTopology τ) :=
  (iteratedSliceBackward_isMorphismOfSites X τ).toIsContinuous

/-- The structure-sheaf map of `associatedRingedSiteEquivMap`, identifying
`𝒪_{slice X}` with the continuous pushforward of `𝒪_𝒳` along
`toFunctor e.inv`. -/
def associatedRingedSiteEquivMap_structureSheafMap
    {𝒳 : GroupoidsOver S} {X : Over S} (e : 𝒳 ≌ slice X)
    (τ : StandardTopology) :
    (associatedStructureSheaf (slice X) τ) ⟶
      ((toFunctor e.inv).sheafPushforwardContinuous RingCat.{u}
        ((slice X).associatedTopology τ) (𝒳.associatedTopology τ)).obj
        (associatedStructureSheaf 𝒳 τ) :=
  (@sheafPushforwardContinuousIso _ _ _ _ _ _
      (eqToIso (comm e.inv).symm) RingCat.{u} _
      ((slice X).associatedTopology τ) (τ.overTopology S)
      (Functor.inheritedTopology.isContinuous (slice X).p (τ.overTopology S))
      (by
        rw [comm e.inv]
        exact Functor.inheritedTopology.isContinuous (slice X).p (τ.overTopology S))).hom.app
    (StandardTopology.Big.structureSheaf τ S)

/-- The morphism of associated `τ`-ringed sites induced by a representing
equivalence `e : 𝒳 ≌ slice X`, with underlying functor `toFunctor e.inv`. -/
def associatedRingedSiteEquivMap {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    RingedSiteMap (𝒳.associatedTopology τ) (associatedStructureSheaf 𝒳 τ)
      ((slice X).associatedTopology τ) (associatedStructureSheaf (slice X) τ) where
  base := toFunctor e.inv
  isMorphismOfSites := toFunctor_inv_isMorphismOfSites e τ
  structureSheafMap := associatedRingedSiteEquivMap_structureSheafMap e τ

/-- The base of `associatedRingedSiteEquivMap e τ` is `toFunctor e.inv`. -/
theorem associatedRingedSiteEquivMap_base {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    (associatedRingedSiteEquivMap e τ).base = toFunctor e.inv :=
  rfl

/-- The structure-sheaf map of `sliceAssociatedRingedSiteMap`, given by the
identity realization triangle
`iteratedSliceBackward ⋙ (slice X).p ⋙ Over.forget S = Over.forget X.left`. -/
def sliceAssociatedRingedSiteMap_structureSheafMap (X : Over S)
    (τ : StandardTopology) :
    (StandardTopology.Big.structureSheaf τ X.left) ⟶
      (X.iteratedSliceBackward.sheafPushforwardContinuous RingCat.{u}
        (τ.overTopology X.left) ((slice X).associatedTopology τ)).obj
        (associatedStructureSheaf (slice X) τ) :=
  ⟨Scheme.Site.structurePresheafMap (Over.forget X.left)
      ((slice X).p ⋙ Over.forget S) X.iteratedSliceBackward (𝟙 _)⟩

/-- The canonical morphism of ringed sites from the associated `τ`-site of
`slice X` to the big `τ`-site of the scheme `X.left`. -/
def sliceAssociatedRingedSiteMap (X : Over S) (τ : StandardTopology) :
    RingedSiteMap ((slice X).associatedTopology τ) (associatedStructureSheaf (slice X) τ)
      (τ.overTopology X.left) (StandardTopology.Big.structureSheaf τ X.left) where
  base := X.iteratedSliceBackward
  isMorphismOfSites := iteratedSliceBackward_isMorphismOfSites X τ
  structureSheafMap := sliceAssociatedRingedSiteMap_structureSheafMap X τ

/-- The base of `sliceAssociatedRingedSiteMap X τ` is `X.iteratedSliceBackward`. -/
theorem sliceAssociatedRingedSiteMap_base (X : Over S) (τ : StandardTopology) :
    (sliceAssociatedRingedSiteMap X τ).base = X.iteratedSliceBackward :=
  rfl

/-- The canonical morphism of ringed sites `(𝒳_τ, 𝒪_𝒳) ⟶ ((Sch/X.left)_τ, 𝒪)`
induced by a representing equivalence `e : 𝒳 ≌ slice X`. -/
def associatedRingedSiteMap {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    RingedSiteMap (𝒳.associatedTopology τ) (associatedStructureSheaf 𝒳 τ)
      (τ.overTopology X.left) (StandardTopology.Big.structureSheaf τ X.left) :=
  RingedSiteMap.comp (associatedRingedSiteEquivMap e τ)
    (sliceAssociatedRingedSiteMap X τ)

/-- The base of `associatedRingedSiteMap e τ` is the composite
`X.iteratedSliceBackward ⋙ toFunctor e.inv`. -/
theorem associatedRingedSiteMap_base {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    (associatedRingedSiteMap e τ).base =
      X.iteratedSliceBackward ⋙ toFunctor e.inv :=
  rfl

/-- `associatedRingedSiteMap e τ` is the composite of the representing
equivalence comparison with the iterated-slice comparison. -/
theorem associatedRingedSiteMap_eq {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    associatedRingedSiteMap e τ =
      RingedSiteMap.comp (associatedRingedSiteEquivMap e τ)
        (sliceAssociatedRingedSiteMap X τ) :=
  rfl

/-- Objectwise, the structure-sheaf map of `sliceAssociatedRingedSiteMap`
is pullback of global sections along the identity of the underlying scheme. -/
theorem sliceAssociatedRingedSiteMap_structureSheafMap_app (X : Over S)
    (τ : StandardTopology) (U : (Over X.left)ᵒᵖ) :
    (sliceAssociatedRingedSiteMap X τ).structureSheafMap.hom.app U =
      RingCat.ofHom
        (𝟙 U.unop.left : U.unop.left ⟶ U.unop.left).appTop.hom :=
  rfl

/-- A representing equivalence induces an equivalence between the associated ringed
site of a category fibred in groupoids and the big ringed site of its representing scheme. -/
theorem associatedRingedSiteMap_isEquivalence {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    (associatedRingedSiteMap e τ).IsEquivalence :=
  sorry

end AlgebraicGeometry.GroupoidsOver
