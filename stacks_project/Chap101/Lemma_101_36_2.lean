/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Unramified.Composition
import StacksCheckRecall

/-!
# Composition of unramified morphisms of algebraic stacks

The composition of a pair of unramified morphisms of algebraic stacks is
unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Unramified

/- Lemma 101.36.2: The composition of unramified morphisms of algebraic stacks
is unramified.

Stacks writes the composition as `g ∘ f`; the Lean composite is `f ≫ g`. -/
@[stacks 0CIU] #check (AlgebraicGeometry.AlgebraicStack.Unramified.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Unramified f] [Unramified g],
    Unramified (f ≫ g))

end AlgebraicGeometry.AlgebraicStack.Unramified
