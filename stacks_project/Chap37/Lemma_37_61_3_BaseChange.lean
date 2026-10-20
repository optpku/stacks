module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.BaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

#check
  (AlgebraicGeometry.LocallyOfType.instIsPerfectRingMapStableUnderFlatBaseChange :
    MorphismProperty.IsStableUnderBaseChangeAgainst
      (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap)
      (@AlgebraicGeometry.Flat : MorphismProperty AlgebraicGeometry.Scheme.{u}))

#check
  (AlgebraicGeometry.LocallyOfType.instIsPerfectRingMapStableAlongFlat :
    ∀ {S' S : AlgebraicGeometry.Scheme.{u}} (g : S' ⟶ S) [AlgebraicGeometry.Flat g],
      MorphismProperty.IsStableUnderBaseChangeAlong
        (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap) g)

#check
  (AlgebraicGeometry.LocallyOfType.isPerfectRingMap_pullback_snd :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
      [AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap f]
      [AlgebraicGeometry.Flat g],
      AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap (pullback.snd f g))
