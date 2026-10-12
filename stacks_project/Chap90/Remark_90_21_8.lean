/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_21_7_Restrict
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u u' v v' w

variable {C : Type u} [Category.{v} C] [HasPullbacks (C ⥤ Type w)]
variable {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
variable (G : GroupoidInFunctors C) (ι : C' ⥤ C)

/- Remark 90.21.8: in the situation of Definition 90.21.7, we often denote the
restricted structure maps s|_{C'}, t|_{C'}, c|_{C'} simply by s, t, c. These are
the fields (G.restrict ι).s, (G.restrict ι).t, and (G.restrict ι).c of the
restricted groupoid in functors. -/
@[stacks 06KA]
#check ((G.restrict ι).s, (G.restrict ι).t, (G.restrict ι).c)
