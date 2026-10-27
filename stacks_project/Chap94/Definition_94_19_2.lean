/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ChangeOfBase
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 94.19.2: let `Sch_fppf` be a big fppf site. Let `g : S ⟶ S'` be a
morphism of this site. If `p : X ⟶ (Sch/S)_fppf` is an algebraic stack over `S`,
then `X` viewed as an algebraic stack over `S'` is the algebraic stack
`X ⟶ (Sch/S')_fppf` given by `AlgebraicStack.viewedOver g X`, i.e. Construction A
of Lemma 94.19.1. Its structure morphism is `X.p ⋙ Over.map g`. -/
@[stacks 04X6] #check (AlgebraicGeometry.AlgebraicStack.viewedOver :
  ∀ {S S' : Scheme.{u}}, (S ⟶ S') → GroupoidsOver S → GroupoidsOver S')

#check (AlgebraicGeometry.AlgebraicStack.viewedOver.algebraicStack :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X : GroupoidsOver S) [AlgebraicStack X],
    AlgebraicStack (AlgebraicStack.viewedOver g X))

#check (AlgebraicGeometry.AlgebraicStack.viewedOver_total :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X : GroupoidsOver S),
    (AlgebraicStack.viewedOver g X).total = X.total)

#check (AlgebraicGeometry.AlgebraicStack.viewedOver_p :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X : GroupoidsOver S),
    (AlgebraicStack.viewedOver g X).p = X.p ⋙ Over.map g)
