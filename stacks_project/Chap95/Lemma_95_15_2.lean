module

import StacksCheckRecall
public import stacks_project.Chap95.Proposition_95_15_3_Quotient

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupAlgebraicSpace
open AlgebraicGeometry.QuotientStack.GroupAction

universe u

/- Lemma 95.15.2: in Situation 95.15.1, up to a replacement as in
Remark 8.4.9, the functor `p : [[X/G]] ⟶ (Sch/S)_fppf` given by
`forget G X` is a stack in groupoids over `(Sch/S)_fppf`. -/
@[stacks 0370] #check
  fun {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
      (X : Action G) ↦
    (instIsStackInGroupoids :
      IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget G X))

/- Remark 8.4.9 condition (4): the fibre of `forget G X` over `U` is
essentially small, so a small model exists via `StackOver.SmallModel`. -/
#check
  fun {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
      (X : Action G) (U : Over S) ↦
    (fibers_essentiallySmall U :
      ObjectProperty.EssentiallySmall.{u}
        (⊤ : ObjectProperty ((forget G X).Fiber U)))
