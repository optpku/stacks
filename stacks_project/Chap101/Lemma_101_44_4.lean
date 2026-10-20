/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocalCompleteIntersection
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.44.4: if `Y ⟶ Z` is smooth and `X ⟶ Z` is a local complete
intersection morphism, then `f : X ⟶ Y` is a local complete intersection
morphism. -/
@[stacks 0CJ6] #check
  (AlgebraicGeometry.AlgebraicStack.IsLocalCompleteIntersection.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [Smooth g] [IsLocalCompleteIntersection (f ≫ g)],
      IsLocalCompleteIntersection f)
