module

public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Underlying topoi of ringed-site morphisms

This module exposes the site-presented morphism of topoi underlying a morphism of ringed sites.
The separate `Topos/TwoMorphism` leaf contains the corresponding structure-sheaf `2`-cell API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe uX vX uY vY w t

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

section PresentedTopos

variable [UnivLE.{max uX vX, t}] [UnivLE.{max uY vX, t}]

/-- The morphism of topoi presented by a morphism of ringed sites. -/
@[stacks 01D3 "(2)"]
noncomputable def toMorphismOfTopoi (f : X.Hom Y)
    [PreservesFiniteLimits
      (f.sheafPullback (A := Type t))] :
    MorphismOfTopoiIn Y.siteTopology X.siteTopology where
  inverseImageFunctor := LeftExactFunctor.of (f.sheafPullback (A := Type t))
  pushforward := f.sheafPushforwardContinuous (A := Type t)
  adjunction := f.sheafAdjunctionContinuous (A := Type t)

/-- The direct image of the topos morphism underlying a ringed-site morphism is the continuous
sheaf pushforward along its base functor. -/
@[simp]
theorem toMorphismOfTopoi_pushforward
    (f : X.Hom Y)
    [PreservesFiniteLimits
      (f.sheafPullback (A := Type t))] :
    (f.toMorphismOfTopoi).pushforward =
      f.sheafPushforwardContinuous (A := Type t) := sorry

/-- The inverse image of the topos morphism underlying a ringed-site morphism is the sheaf
pullback along its base functor. -/
@[simp]
theorem toMorphismOfTopoi_inverseImage
    (f : X.Hom Y)
    [PreservesFiniteLimits
      (f.sheafPullback (A := Type t))] :
    (f.toMorphismOfTopoi).inverseImage =
      f.sheafPullback (A := Type t) := sorry

end PresentedTopos

/-- A ringed-site morphism is an equivalence when its inverse image on underlying topoi and its
structure-sheaf map are both invertible.  The inverse image is tested in the canonical universe
large enough for both site presentations, so this property has no ambiguous universe parameter. -/
@[stacks 03CR "ringed equivalence criterion"]
class IsRingedEquivalence (f : X.Hom Y) : Prop where
  /-- The inverse-image functor of the underlying morphism of topoi is an equivalence. -/
  inverseImage_isEquivalence :
    Functor.IsEquivalence
      (f.sheafPullback (A := Type (max uX vX uY vY)))
  /-- The structure-sheaf map is an isomorphism. -/
  structureSheafMap_isIso : IsIso f.structureSheafMap


section PresentedTopos

variable [UnivLE.{max uX vX, t}] [UnivLE.{max uY vX, t}]

/-- A ringed equivalence induces an equivalence on the inverse-image functor of its underlying
morphism of topoi. -/
theorem toMorphismOfTopoi_inverseImage_isEquivalence
    (f : X.Hom Y)
    [PreservesFiniteLimits
      (f.sheafPullback (A := Type t))]
    [f.IsRingedEquivalence] :
    Functor.IsEquivalence (f.toMorphismOfTopoi).inverseImage := sorry


end PresentedTopos

end RingedSite.Hom
