/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.35.6: let `X`, `Y` be algebraic stacks étale over an algebraic stack
`Z`. Any morphism `X ⟶ Y` over `Z` is étale. -/
@[stacks 0CIR] #check
  (AlgebraicGeometry.AlgebraicStack.Etale.of_two_commute :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (α : p ≅ f ≫ q)
      [Etale p] [Etale q],
      Etale f)
