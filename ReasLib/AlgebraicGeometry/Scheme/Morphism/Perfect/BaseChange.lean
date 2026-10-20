module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.BaseChange
public import ReasLib.RingTheory.RingHom.Perfect.BaseChange

/-!
# Flat base change of perfect scheme morphisms

Scheme morphisms locally induced by perfect ring maps are preserved by base change along flat
morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.LocallyOfType

/-- Scheme morphisms locally induced by perfect ring maps are stable under flat base change. -/
instance instIsPerfectRingMapStableUnderFlatBaseChange :
    MorphismProperty.IsStableUnderBaseChangeAgainst
      (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap)
      (@AlgebraicGeometry.Flat : MorphismProperty Scheme.{u}) := sorry

/-- Scheme morphisms locally induced by perfect ring maps are stable under base change along a
fixed flat morphism. -/
instance instIsPerfectRingMapStableAlongFlat
    {S' S : Scheme.{u}} (g : S' ⟶ S) [Flat g] :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap) g := sorry

/-- The second projection from the pullback of a morphism locally induced by perfect ring maps
along a flat morphism is again locally induced by perfect ring maps. -/
instance isPerfectRingMap_pullback_snd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap f] [Flat g] :
    AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap (pullback.snd f g) := sorry

end AlgebraicGeometry.LocallyOfType
