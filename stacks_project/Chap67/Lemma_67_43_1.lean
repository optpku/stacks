/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Separated
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.43.1: If a morphism of algebraic spaces is separated, then it
satisfies the uniqueness part of the valuative criterion. -/
@[stacks 03KU] #check
  (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Uniqueness.of_separated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Separated f], ValuativeCriterion.Uniqueness f)

#check
  (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Uniqueness.liftStruct_eq_of_separated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [Separated f]
      (sq : ValuativeCommSq f) (l₁ l₂ : sq.commSq.LiftStruct), l₁ = l₂)
