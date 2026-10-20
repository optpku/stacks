/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Quotient.Category

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupAlgebraicSpace
open AlgebraicGeometry.QuotientStack.GroupAction

universe u

/- Lemma 95.15.2: in Situation 95.15.1, up to a replacement as in
Remark 8.4.9, the functor `p : [[X/G]] ⟶ (Sch/S)_fppf` given by
`forget G X` is a stack in groupoids over `(Sch/S)_fppf`. -/
@[stacks 0370] #check
  (AlgebraicGeometry.QuotientStack.GroupAction.instIsStackInGroupoids :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
      {G : GroupAlgebraicSpace B} {X : Action G},
      IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget G X))

/- Remark 8.4.9 condition (4): the fibre of `forget G X` over `U` is
essentially small, so a small model exists via `StackOver.SmallModel`. -/
#check
  (AlgebraicGeometry.QuotientStack.GroupAction.fibers_essentiallySmall :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
      {G : GroupAlgebraicSpace B} {X : Action G} (U : Over S),
      ObjectProperty.EssentiallySmall.{u}
        (⊤ : ObjectProperty ((forget G X).Fiber U)))
