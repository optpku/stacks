/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Unramified

/-!
# Cancellation of unramifiedness against DM postcomposition

If a composite morphism of algebraic stacks is unramified and the second
factor is DM, then the first factor is unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Unramified

/-- If a composite morphism of algebraic stacks is unramified and the second
factor is DM, then the first factor is unramified. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [Unramified (f ≫ g)] [DM g] : Unramified f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Unramified
