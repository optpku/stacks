/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap78.Definition_78_5_1_Group

/-!
# Braiding on slices of algebraic spaces

The Cartesian monoidal structure on `Over B` for `B : AlgebraicSpace S` is
supplied by `instCartesianMonoidalCategoryOver`. This module adds the
induced braiding.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- The canonical braiding on slices of algebraic spaces is provided by the shared owner. -/
#check (AlgebraicGeometry.AlgebraicSpace.instBraidedCategoryOver :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S), BraidedCategory (Over B))

end AlgebraicGeometry.AlgebraicSpace
