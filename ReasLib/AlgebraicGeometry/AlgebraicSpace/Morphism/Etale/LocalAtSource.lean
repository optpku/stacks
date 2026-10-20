module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage

/-!
# Étale morphisms are étale local on the source

Étaleness of morphisms of algebraic spaces is local on the source for the
étale precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale

/-- Étaleness of morphisms of algebraic spaces is local on the source for
the étale precoverage. -/
instance isLocalAtSourceEtale {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@Etale S : MorphismProperty (AlgebraicSpace S))
      (etalePrecoverage (S := S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale
