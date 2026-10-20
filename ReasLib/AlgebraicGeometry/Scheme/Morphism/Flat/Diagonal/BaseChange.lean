module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Flat diagonals under base change

This module records that flatness of a diagonal morphism is preserved by canonical base
change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Flat

/-- Flatness of the diagonal of a scheme morphism is preserved by canonical base change. -/
theorem diagonal_baseChange {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : Flat (pullback.diagonal f)) :
    Flat (pullback.diagonal (pullback.fst g f)) := sorry

end AlgebraicGeometry.Flat
