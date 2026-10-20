module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Formally unramified morphisms and base change

Formal unramifiedness of scheme morphisms is preserved by arbitrary base change.
-/

namespace AlgebraicGeometry.FormallyUnramified

/-- Formal unramifiedness of scheme morphisms is stable under arbitrary base change. -/
public theorem isStableUnderBaseChange :
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange
      @AlgebraicGeometry.FormallyUnramified :=
  AlgebraicGeometry.FormallyUnramified.instIsStableUnderBaseChangeScheme

end AlgebraicGeometry.FormallyUnramified
