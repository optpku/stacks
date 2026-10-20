/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocalCompleteIntersection.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.44.3: a flat base change of a local complete intersection morphism
is a local complete intersection morphism.

Stacks writes the base change as `Y' ×_Y X ⟶ Y'`; the Lean projection is
`TwoFibreProduct.snd f g` of a local complete intersection morphism `f : X ⟶ Y`
along a flat morphism `g : Z ⟶ Y`. -/
@[stacks 0CJ5] #check
  (AlgebraicGeometry.AlgebraicStack.IsLocalCompleteIntersection.twoFibreProduct_snd :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Z ⟶ Y)
      [IsLocalCompleteIntersection f] [Flat g],
      IsLocalCompleteIntersection (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))
