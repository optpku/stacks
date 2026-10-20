module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Normalized

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup.hom :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] (s : NormalizedBlowup X),
    s.source ⟶ X)
