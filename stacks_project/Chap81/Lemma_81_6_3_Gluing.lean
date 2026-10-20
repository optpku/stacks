module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

universe u

/- Base change along a thickening–affine pushout takes algebraic spaces over the pushout
into compatible pairs over its two components. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing.baseChange :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f],
      Over (pushout i f) ⥤ CategoricalPullback (Over.pullback f) (Over.pullback i))
