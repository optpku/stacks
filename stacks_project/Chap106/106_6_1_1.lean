/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Object
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- 106.6.1.1: an object of the category of lifts along a thickening
`iX : X ⟶ X'` of algebraic stacks and a smooth map `x : W.toGroupoids ⟶ X`
from an algebraic space is a system `(U, U', a, i, x', α)` giving the
2-commutative diagram `U —i→ U'`, `U —a→ W —x→ X —iX→ X'`, `U' —x'→ X'`,
with square 2-cell `α` after composing `x ∘ a` with `iX`, `a` étale,
`x'` smooth, and `U = X ×_{X'} U'`. -/
@[stacks 0CJQ] #check (AlgebraicGeometry.AlgebraicStack.Lift.Object :
  ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack X']
    (iX : X ⟶ X') [IsThickening iX] {W : AlgebraicSpace S}
    (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x], Type (u + 1))
