/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Uniqueness

/-!
# Separated morphisms satisfy uniqueness in the valuative criterion

A separated morphism of algebraic stacks satisfies the uniqueness part of the
valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.ValuativeCriterion

/-- A separated morphism of algebraic stacks satisfies the uniqueness part of
the valuative criterion. -/
@[stacks 0CLU]
instance Uniqueness.of_separated {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Separated f] :
    Uniqueness f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
