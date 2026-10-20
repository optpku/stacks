module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.LocalRingAtPoint

@[expose] public section

open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicStack.localRingDimAt :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.IsLocallyNoetherian X] (x : AlgebraicStack.Points X),
    AlgebraicStack.IsFiniteTypePoint x → EInt)
