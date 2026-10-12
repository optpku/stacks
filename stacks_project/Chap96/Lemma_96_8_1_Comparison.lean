/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.RingedSite.Topos
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
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

/-- The inverse of a representing equivalence `e : 𝒳 ≌ slice X` is a morphism of
associated `τ`-sites: `toFunctor e.inv` is an equivalence, hence representably
flat, and cartesian functors are continuous for inherited topologies. -/
instance toFunctor_inv_isMorphismOfSites {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    IsMorphismOfSites ((slice X).associatedTopology τ) (𝒳.associatedTopology τ)
      (toFunctor e.inv) :=
  sorry

/-- The composite `toFunctor f ⋙ 𝒴.p` is continuous from the associated
`τ`-topology of `𝒳` to the big `τ`-site of `S`. -/
instance toFunctor_comp_p_isContinuous {𝒳 𝒴 : GroupoidsOver S} (f : 𝒳 ⟶ 𝒴)
    (τ : StandardTopology) :
    (toFunctor f ⋙ 𝒴.p).IsContinuous (𝒳.associatedTopology τ)
      (τ.overTopology S) :=
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
  (sheafPushforwardContinuousIso (eqToIso (comm e.inv).symm) RingCat.{u}
      ((slice X).associatedTopology τ) (τ.overTopology S)).hom.app
    (StandardTopology.Big.structureSheaf τ S)

/-- The morphism of associated `τ`-ringed sites induced by a representing
equivalence `e : 𝒳 ≌ slice X`, with underlying functor `toFunctor e.inv`. -/
def associatedRingedSiteEquivHom {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    RingedSite.Hom (associatedRingedSite 𝒳 τ)
      (associatedRingedSite (slice X) τ) where
  base := toFunctor e.inv
  isMorphismOfSites := toFunctor_inv_isMorphismOfSites e τ
  structureSheafMap := associatedRingedSiteEquivHom_structureSheafMap e τ

/-- The base of `associatedRingedSiteEquivHom e τ` is `toFunctor e.inv`. -/
theorem associatedRingedSiteEquivHom_base {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    (associatedRingedSiteEquivHom e τ).base = toFunctor e.inv :=
  sorry

/-- The structure-sheaf map of `sliceAssociatedRingedSiteHom`, given by the
identity realization triangle
`iteratedSliceBackward ⋙ (slice X).p ⋙ Over.forget S = Over.forget X.left`. -/
def sliceAssociatedRingedSiteHom_structureSheafMap (X : Over S)
    (τ : StandardTopology) :
    (StandardTopology.Big.ringedSite τ X.left).structureSheaf ⟶
      (X.iteratedSliceBackward.sheafPushforwardContinuous RingCat.{u}
        (τ.overTopology X.left) ((slice X).associatedTopology τ)).obj
        (associatedRingedSite (slice X) τ).structureSheaf :=
  ⟨Scheme.Site.structurePresheafMap (Over.forget X.left)
      ((slice X).p ⋙ Over.forget S) X.iteratedSliceBackward (𝟙 _)⟩

/-- The canonical morphism of ringed sites from the associated `τ`-site of
`slice X` to the big `τ`-site of the scheme `X.left`. -/
def sliceAssociatedRingedSiteHom (X : Over S) (τ : StandardTopology) :
    RingedSite.Hom (associatedRingedSite (slice X) τ)
      (StandardTopology.Big.ringedSite τ X.left) where
  base := X.iteratedSliceBackward
  isMorphismOfSites := iteratedSliceBackward_isMorphismOfSites X τ
  structureSheafMap := sliceAssociatedRingedSiteHom_structureSheafMap X τ

/-- The base of `sliceAssociatedRingedSiteHom X τ` is `X.iteratedSliceBackward`. -/
theorem sliceAssociatedRingedSiteHom_base (X : Over S) (τ : StandardTopology) :
    (sliceAssociatedRingedSiteHom X τ).base = X.iteratedSliceBackward :=
  sorry

/-- The canonical morphism of ringed sites `(𝒳_τ, 𝒪_𝒳) ⟶ ((Sch/X.left)_τ, 𝒪)`
induced by a representing equivalence `e : 𝒳 ≌ slice X`. -/
def associatedRingedSiteHom {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    RingedSite.Hom (associatedRingedSite 𝒳 τ)
      (StandardTopology.Big.ringedSite τ X.left) :=
  RingedSite.Hom.comp (associatedRingedSiteEquivHom e τ)
    (sliceAssociatedRingedSiteHom X τ)

/-- The base of `associatedRingedSiteHom e τ` is the composite
`X.iteratedSliceBackward ⋙ toFunctor e.inv`. -/
theorem associatedRingedSiteHom_base {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    (associatedRingedSiteHom e τ).base =
      X.iteratedSliceBackward ⋙ toFunctor e.inv :=
  sorry

/-- `associatedRingedSiteHom e τ` is the composite of the representing
equivalence comparison with the iterated-slice comparison. -/
theorem associatedRingedSiteHom_eq {𝒳 : GroupoidsOver S} {X : Over S}
    (e : 𝒳 ≌ slice X) (τ : StandardTopology) :
    associatedRingedSiteHom e τ =
      RingedSite.Hom.comp (associatedRingedSiteEquivHom e τ)
        (sliceAssociatedRingedSiteHom X τ) :=
  sorry

/-- Objectwise, the structure-sheaf map of `sliceAssociatedRingedSiteHom`
is pullback of global sections along the identity of the underlying scheme. -/
theorem sliceAssociatedRingedSiteHom_structureSheafMap_app (X : Over S)
    (τ : StandardTopology) (U : (Over X.left)ᵒᵖ) :
    (sliceAssociatedRingedSiteHom X τ).structureSheafMap.hom.app U =
      RingCat.ofHom
        (𝟙 U.unop.left : U.unop.left ⟶ U.unop.left).appTop.hom :=
  sorry

end AlgebraicGeometry.GroupoidsOver
