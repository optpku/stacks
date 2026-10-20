module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage

/-!
# Unramified morphisms are étale local on the source

Unramifiedness of morphisms of algebraic spaces is local on the source for the
étale precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Unramified

/-- Unramifiedness of morphisms of algebraic spaces is local on the source for
the étale precoverage. -/
instance isLocalAtSourceEtale {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@Unramified S : MorphismProperty (AlgebraicSpace S))
      (etalePrecoverage (S := S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Unramified
