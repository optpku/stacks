/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyClosed

/-!
# Base change of universally closed morphisms of algebraic stacks

The base change of a universally closed morphism of algebraic stacks by any
morphism of algebraic stacks is universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.13.3: The base change of a universally closed morphism of algebraic
stacks by any morphism of algebraic stacks is universally closed.

Stacks writes the base change as `Z ×_Y X ⟶ Z`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 0514] #check
  (AlgebraicGeometry.AlgebraicStack.universallyClosed_pullback_snd :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Z ⟶ Y) [UniversallyClosed f],
      UniversallyClosed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

end AlgebraicGeometry.AlgebraicStack
