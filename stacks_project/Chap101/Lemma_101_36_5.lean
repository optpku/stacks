/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Unramified.Immersion
import StacksCheckRecall

/-!
# Immersions of algebraic stacks are unramified
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.36.5: An immersion of algebraic stacks is unramified. -/
@[stacks 0CIX] #check (AlgebraicGeometry.AlgebraicStack.unramified_of_immersion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Groupoids.Hom.Immersion f], AlgebraicStack.Unramified f)
