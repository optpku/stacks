/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.Hom
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- 106.6.1.2: a morphism of lifts `(f, f', γ)` from `(V, V', b, j, y')` to
`(U, U', a, i, x')` over `W`, displayed as the 2-commutative diagram with
space maps `f : V ⟶ U` over `W` (so `f ≫ a = b`), `f' : V' ⟶ U'` restricting
to `f` (so `j ≫ f' = f ≫ i`), and 2-cell `γ : toGroupoids.map f' ≫ x' ≅ y'`
in the right triangle. -/
@[stacks 0CJR] #check (AlgebraicGeometry.AlgebraicStack.Lift.Hom :
  ∀ {S : Scheme.{u}} {X' : GroupoidsOver S} [AlgebraicStack X']
    {W U U' V V' : AlgebraicSpace S},
    (U ⟶ W) → (U ⟶ U') → (U'.toGroupoids ⟶ X') →
    (V ⟶ W) → (V ⟶ V') → (V'.toGroupoids ⟶ X') → Type (u + 1))
