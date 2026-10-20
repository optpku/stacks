/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange

/-!
# Decency along representable morphisms of algebraic stacks

Decency of the target implies decency of the source for morphisms representable
by schemes, and for quasi-separated morphisms representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The source of a morphism of algebraic stacks representable by schemes is
decent if its target is decent. -/
@[stacks 0GW3]
theorem IsDecent.of_relativelyRepresentable {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (hf : FiberedCategoryOver.Groupoids.relativelyRepresentable f)
    [IsDecent Y] : IsDecent X :=
  sorry

/-- The source of a quasi-separated morphism of algebraic stacks representable
by algebraic spaces is decent if its target is decent. -/
@[stacks 0GW3]
theorem IsDecent.of_relativelyRepresentableByAlgebraicSpaces {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f)
    [IsDecent Y] [QuasiSeparated f] : IsDecent X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
