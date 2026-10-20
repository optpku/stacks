module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeSquare

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq :
    {S : AlgebraicGeometry.Scheme.{u}} →
    {X Y : AlgebraicGeometry.GroupoidsOver S} →
    [AlgebraicGeometry.AlgebraicStack X] →
    [AlgebraicGeometry.AlgebraicStack Y] → (X ⟶ Y) → Type (u + 1))
