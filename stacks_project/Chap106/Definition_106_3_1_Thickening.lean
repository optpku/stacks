/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening

/-!
# Thickenings of algebraic stacks

A morphism of algebraic stacks is a thickening when it is a closed immersion
and surjective on associated points, so the source is a closed substack whose
associated point space agrees with the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Definition 106.3.1 (1): an algebraic stack `X'` is a thickening of an
algebraic stack `X` if `X` is a closed substack of `X'` and the associated
topological spaces are equal. -/
#check (AlgebraicGeometry.AlgebraicStack.IsThickening :
  {S : Scheme.{u}} → {X X' : GroupoidsOver S} →
    [AlgebraicStack X] → [AlgebraicStack X'] → (X ⟶ X') → Prop)
