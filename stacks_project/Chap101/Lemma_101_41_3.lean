/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Separated
import StacksCheckRecall

/-!
# Separated morphisms satisfy uniqueness in the valuative criterion

A separated morphism of algebraic stacks has a thin dotted-arrow category with
at most one isomorphism class in every solid valuative square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.41.3: If `f : X ⟶ Y` is a separated morphism of algebraic stacks,
then `f` satisfies the uniqueness part of the valuative criterion. -/
@[stacks 0CLU] #check (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness.of_separated :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicStack.Separated f],
    AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness f)
