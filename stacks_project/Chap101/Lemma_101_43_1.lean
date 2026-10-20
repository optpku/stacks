/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Proper.ValuativeCriterion
import StacksCheckRecall

/-!
# Valuative criterion for properness

A finite-type quasi-separated morphism of algebraic stacks is proper if and
only if it satisfies both the uniqueness and existence parts of the valuative
criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.43.1: Let `f : X ⟶ Y` be a morphism of algebraic stacks. Assume
`f` is of finite type and quasi-separated. Then `f` is proper if and only if
`f` satisfies both the uniqueness and existence parts of the valuative
criterion. -/
@[stacks 0CLZ] #check (AlgebraicGeometry.AlgebraicStack.Proper.iff_valuativeCriterion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.FiniteType f] [AlgebraicStack.QuasiSeparated f],
    AlgebraicStack.Proper f ↔ AlgebraicStack.ValuativeCriterion.Uniqueness f ∧
      AlgebraicStack.ValuativeCriterion.Existence f)

#check (AlgebraicGeometry.AlgebraicStack.Proper.of_valuativeCriterion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.FiniteType f] [AlgebraicStack.QuasiSeparated f]
    [AlgebraicStack.ValuativeCriterion.Uniqueness f]
    [AlgebraicStack.ValuativeCriterion.Existence f], AlgebraicStack.Proper f)
