/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.Comparison.Construction
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell

/-!
# Inertia comparison of an unramified morphism

The canonical inertia comparison of an unramified morphism of algebraic stacks
is an equivalence if and only if it induces isomorphisms on automorphism groups
at every point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Inertia

/-- The canonical inertia comparison of an unramified morphism of algebraic
stacks is an equivalence over the base if and only if the morphism induces an
isomorphism of automorphism groups at every point of the source. -/
@[stacks 0DU9]
theorem comparison_isEquivalence_iff_forall_isIsoAt {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Unramified f] :
    (toBasedFunctor (comparison f)).IsEquivalence ↔
      ∀ x : |X|, automorphismGroup.IsIsoAt f x :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Inertia
