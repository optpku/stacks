/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Groupoid.InFunctors.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory Functor Limits

universe u u' v v' w

variable {C : Type u} [Category.{v} C] [HasPullbacks (C ⥤ Type w)]
variable {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
variable (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C)

/- Remark 90.21.8: in the situation of Definition 90.21.7, we often denote the
restricted structure maps s|_{C'}, t|_{C'}, c|_{C'} simply by s, t, c. These are
the fields (G.restrict ι).s, (G.restrict ι).t, and (G.restrict ι).c of the
restricted groupoid in functors. -/
@[stacks 06KA]
#check (CategoryTheory.GroupoidInFunctors.restrict_spec G ι :
  (G.restrict ι).U = ι ⋙ G.U ∧
    (G.restrict ι).R = ι ⋙ G.R ∧
    (G.restrict ι).s = whiskerLeft ι G.s ∧
    (G.restrict ι).t = whiskerLeft ι G.t ∧
    (G.restrict ι).c =
      (PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c ∧
    (G.restrict ι).e = whiskerLeft ι G.e ∧
    (G.restrict ι).i = whiskerLeft ι G.i)
