module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.PseudoCatenary

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicStack.IsPseudoCatenary :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S)
    [AlgebraicGeometry.AlgebraicStack X], Prop)
