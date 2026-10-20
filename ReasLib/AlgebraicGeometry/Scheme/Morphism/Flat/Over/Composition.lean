/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat morphisms in over categories

This module provides flatness of the underlying scheme morphism of a composite
in an over category.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Flat

/-- The underlying scheme morphism of a composite of flat morphisms in an over
category is flat. -/
instance overComp {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f.left] [Flat g.left] :
    Flat (f ≫ g).left := by
  rw [Over.comp_left]
  exact AlgebraicGeometry.Flat.comp f.left g.left

end AlgebraicGeometry.Flat
