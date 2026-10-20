module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents

@[expose] public section

open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.codimZeroPoints :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), Set (AlgebraicSpace.Points X))
