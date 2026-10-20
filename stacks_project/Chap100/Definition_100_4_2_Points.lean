module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicStack.Points :
  {S : AlgebraicGeometry.Scheme.{u}} → (X : AlgebraicGeometry.GroupoidsOver S) →
    [AlgebraicGeometry.AlgebraicStack X] → Type (u + 1))
