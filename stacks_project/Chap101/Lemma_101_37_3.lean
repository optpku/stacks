/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Proper.Composition
import StacksCheckRecall

/-!
# Composition of proper morphisms of algebraic stacks

A composition of proper morphisms of algebraic stacks is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.37.3: A composition of proper morphisms is proper.

Stacks writes the composition as `g ∘ f`; the Lean composite is `f ≫ g`. -/
@[stacks 0CL7] #check (AlgebraicGeometry.AlgebraicStack.Proper.comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicStack.Proper f] [AlgebraicStack.Proper g],
    AlgebraicStack.Proper (f ≫ g))
