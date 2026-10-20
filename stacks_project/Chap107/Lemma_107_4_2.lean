/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap107.Lemma_107_4_2_ComponentsMap
import StacksCheckRecall

/-!
# Formal branches surject onto irreducible components through a point

In the situation of Definition 107.4.1, the canonical map from formal branches
of `X` through `x0` onto irreducible components of `|X|` containing `x0` is
surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.FormalBranches

/- Lemma 107.4.2: In the situation of Definition 107.4.1 there is a canonical
surjection from the set of formal branches of `X` through `x0` to the set of
irreducible components of `|X|` containing `x0` in `|X|`. -/
@[stacks 0DRB]
#check (AlgebraicGeometry.AlgebraicStack.FormalBranches.range_toComponent :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyOfFiniteType X]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ),
    Set.range (toComponent x0 hτ) =
      @irreducibleComponentsAt (Points X) τ (Points.mk x0))

end AlgebraicGeometry.AlgebraicStack.FormalBranches
