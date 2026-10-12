/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.LocallyOfType

/-- Scheme morphisms locally induced by local-complete-intersection ring maps are stable under
base change along flat morphisms. -/
instance instIsLocalCompleteIntersectionStableUnderFlatBaseChange :
    MorphismProperty.IsStableUnderBaseChangeAgainst
      (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsLocalCompleteIntersection)
      (@AlgebraicGeometry.Flat : MorphismProperty Scheme.{u}) := sorry

/-- Scheme morphisms locally induced by local-complete-intersection ring maps are stable under
base change along a fixed flat morphism. -/
instance instIsLocalCompleteIntersectionStableAlongFlat
    {S' S : Scheme.{u}} (g : S' ⟶ S) [Flat g] :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsLocalCompleteIntersection) g := sorry

/-- The second projection from the pullback of a morphism locally induced by a
local-complete-intersection ring map along a flat morphism has the same property. -/
instance isLocalCompleteIntersection_pullback_snd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f] [Flat g] :
    AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection
      (pullback.snd f g) := sorry

end AlgebraicGeometry.LocallyOfType
