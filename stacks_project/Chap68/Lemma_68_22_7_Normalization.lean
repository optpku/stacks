module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Decent

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens.of_isDecent :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsDecent X] [HasFiniteIrreducibleComponents X],
      HasFiniteIrreducibleComponentsOnCompactOpens X)

#check
  (AlgebraicGeometry.AlgebraicSpace.instIsDecent_normalization :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsDecent X] [HasFiniteIrreducibleComponents X],
      IsDecent X.normalization)

#check
  (AlgebraicGeometry.AlgebraicSpace.instHasFiniteIrreducibleComponents_normalization :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsDecent X] [HasFiniteIrreducibleComponents X],
      HasFiniteIrreducibleComponents X.normalization)
