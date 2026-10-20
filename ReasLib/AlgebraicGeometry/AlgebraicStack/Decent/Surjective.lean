/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective

/-!
# Descent of decency along quasi-compact surjections

Decency descends along quasi-compact surjective morphisms of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The target of a quasi-compact surjective morphism from a decent algebraic
stack is decent. -/
theorem IsDecent.of_quasiCompact_surjective {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [Surjective f] [IsDecent X] : IsDecent Y :=
  sorry

end AlgebraicGeometry.AlgebraicStack
