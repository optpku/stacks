/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness

/-!
# Uniqueness part of the valuative criterion for algebraic stacks

A morphism of algebraic stacks satisfies uniqueness when every valuative
2-commutative square has a thin dotted-arrow category with at most one
isomorphism class. This property is stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)

