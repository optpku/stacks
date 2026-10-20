/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations

/-!
# Relative dimension in over categories

This module provides the relative dimension of the underlying scheme morphism
of a composite in an over category.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The underlying scheme morphism of a composite has the sum of the relative
dimensions when its first factor is flat. -/
instance instRelativeDimensionOverCompOfFlat
    {S : Scheme.{u}} {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) {r s : ℕ}
    [RelativeDimension f.left r] [RelativeDimension g.left s] [Flat f.left] :
    RelativeDimension (f ≫ g).left (r + s) := by
  rw [Over.comp_left]
  exact relativeDimension_comp_of_flat f.left g.left

end AlgebraicGeometry.Scheme.Hom
