/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.Comparison.Construction

/-!
# Stabilizer-preserving morphisms of algebraic stacks

A morphism of algebraic stacks whose canonical inertia comparison is an
isomorphism is representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks whose canonical inertia comparison
`I_X ⟶ X ×_Y I_Y` is an isomorphism of stacks is representable by algebraic
spaces. -/
@[stacks 0DU7]
theorem relativelyRepresentableByAlgebraicSpaces_of_isEquivalence_comparison
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y)
    (hf : (toBasedFunctor (Inertia.comparison f)).IsEquivalence) :
    relativelyRepresentableByAlgebraicSpaces f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
