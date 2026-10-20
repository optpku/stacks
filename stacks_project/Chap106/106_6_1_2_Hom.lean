module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Hom

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicStack.Lift.Hom :
  ∀ {S : Scheme.{u}} {X' : GroupoidsOver S} [AlgebraicStack X']
    {W U U' V V' : AlgebraicSpace S},
    (U ⟶ W) → (U ⟶ U') → (U'.toGroupoids ⟶ X') →
    (V ⟶ W) → (V ⟶ V') → (V'.toGroupoids ⟶ X') → Type (u + 1))
