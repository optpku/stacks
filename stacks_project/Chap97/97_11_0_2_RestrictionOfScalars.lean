module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

/-! A compatibility bridge for the restriction-of-scalars API. -/

open CategoryTheory AlgebraicGeometry Opposite

universe u

#check (AlgebraicGeometry.AlgebraicSpace.restrictionOfScalars :
  ∀ {S : Scheme.{u}} {X Z B : AlgebraicSpace S},
    (X ⟶ Z) → (Z ⟶ B) → ((Over S)ᵒᵖ ⥤ Type (u + 1)))
