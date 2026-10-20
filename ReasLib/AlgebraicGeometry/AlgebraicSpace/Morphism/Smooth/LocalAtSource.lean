module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Precoverage

/-!
# Smooth-source-locality of smooth morphisms of algebraic spaces

Smoothness of morphisms of algebraic spaces is local on the source for the
precoverage of jointly surjective families of smooth morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Smooth

/-- Smoothness of morphisms of algebraic spaces is local on the source for the
precoverage of jointly surjective families of smooth morphisms. -/
instance isLocalAtSourceSmooth {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@Smooth S : MorphismProperty (AlgebraicSpace S))
      (precoverage (@Smooth S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Smooth
