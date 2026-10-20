/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyOpen
import StacksCheckRecall

/-!
# Base change of universally open morphisms of algebraic stacks

The base change of a universally open morphism of algebraic stacks by any
morphism of algebraic stacks is universally open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 101.11.3: The base change of a universally open morphism of algebraic
stacks by any morphism of algebraic stacks is universally open. -/
@[stacks 06U3] #check (AlgebraicGeometry.AlgebraicStack.universallyOpen_pullback_snd :
  {S : Scheme.{u}} → {X Y Z : GroupoidsOver S} →
    [AlgebraicStack X] → [AlgebraicStack Y] → [AlgebraicStack Z] →
    (f : X ⟶ Y) → (g : Z ⟶ Y) → [AlgebraicStack.UniversallyOpen f] →
    AlgebraicStack.UniversallyOpen (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))
