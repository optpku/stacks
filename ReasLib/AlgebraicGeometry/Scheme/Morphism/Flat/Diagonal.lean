/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Flat diagonals

This module records the behavior of flat diagonal morphisms under composition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Flat

/-- The diagonal of a composite of scheme morphisms is flat when the diagonals of both
factors are flat. -/
theorem diagonal_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Flat (pullback.diagonal f)) (hg : Flat (pullback.diagonal g)) :
    Flat (pullback.diagonal (f ≫ g)) := sorry

end AlgebraicGeometry.Flat
