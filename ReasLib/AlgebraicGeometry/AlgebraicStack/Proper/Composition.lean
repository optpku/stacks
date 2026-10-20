/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Proper

/-!
# Composition of proper morphisms of algebraic stacks

A composition of proper morphisms of algebraic stacks is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Proper

/-- A composition of proper morphisms of algebraic stacks is proper. -/
@[stacks 0CL7]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Proper f] [Proper g] :
    Proper (f ≫ g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Proper
