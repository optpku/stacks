module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Base change of closed immersions of algebraic spaces

Closed immersions of algebraic spaces are stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion

/-- Closed immersions of algebraic spaces are stable under arbitrary base change. -/
instance isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicSpace.IsClosedImmersion S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion
