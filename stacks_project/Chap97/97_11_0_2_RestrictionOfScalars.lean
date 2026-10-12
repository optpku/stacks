/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

/-! A compatibility bridge for the restriction-of-scalars API. -/

open CategoryTheory AlgebraicGeometry Opposite

universe u

#check (AlgebraicGeometry.AlgebraicSpace.restrictionOfScalars :
  ∀ {S : Scheme.{u}} {X Z B : AlgebraicSpace S},
    (X ⟶ Z) → (Z ⟶ B) → ((Over S)ᵒᵖ ⥤ Type (u + 1)))
