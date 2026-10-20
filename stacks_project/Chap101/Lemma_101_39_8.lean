/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.39.8: the composition of morphisms of algebraic stacks which
satisfy the uniqueness part of the valuative criterion is another morphism
of algebraic stacks which satisfies the uniqueness part of the valuative
criterion. -/
@[stacks 0CLI] #check
  (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness.comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [ValuativeCriterion.Uniqueness f] [ValuativeCriterion.Uniqueness g],
      ValuativeCriterion.Uniqueness (f ≫ g))
