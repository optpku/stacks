/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Counterexample
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory
namespace BasedCategory.PseudoPullback.TwoArrowCounterexample

open CategoryTheory.Limits
open scoped CategoricalPullback

variable (g : TwoArrowGroup)
variable (P : (PseudoPullback pointOverBase.toBase pointOverBase.toBase).obj)

/- Example 4.32.4 (1): every arrow of the two-arrow group occurs as the comparison isomorphism
of an object of the ordinary categorical pullback. -/
@[stacks 0H2D "arbitrary comparison arrows in the categorical pullback"]
#check (ordinaryPullbackPoint_iso_hom g : (ordinaryPullbackPoint g).iso.hom = g)

/- Example 4.32.4 (2): the ordinary categorical pullback of the one-point category with itself
over the two-arrow groupoid is discrete. -/
@[stacks 0H2D "ordinary categorical pullback is discrete"]
#check (ordinaryPullbackIsDiscrete : IsDiscrete (pointToBase ⊡ pointToBase))

/- Example 4.32.4 (3): the ordinary categorical pullback has exactly two objects. -/
@[stacks 0H2D "ordinary categorical pullback has two objects"]
#check (ordinaryPullbackNatCard : Nat.card (pointToBase ⊡ pointToBase) = 2)

/- Example 4.32.4 (4): every object of the pseudo-pullback in `Cat/TwoArrowGroupoid` is the
identity-comparison point. -/
@[stacks 0H2D "over-base pullback has only the identity comparison point"]
#check (basedPullback_eq_point P : P = basedPullbackPoint)

/- Example 4.32.4 (5): the pseudo-pullback formed in `Cat/TwoArrowGroupoid` is discrete. -/
@[stacks 0H2D "pullback in the over-category is discrete"]
#check (basedPullbackIsDiscrete :
  IsDiscrete (PseudoPullback pointOverBase.toBase pointOverBase.toBase).obj)

/- Example 4.32.4 (6): the pseudo-pullback formed in `Cat/TwoArrowGroupoid` has exactly one
object. -/
@[stacks 0H2D "pullback in the over-category has one object"]
#check (basedPullbackNatCard :
  Nat.card (PseudoPullback pointOverBase.toBase pointOverBase.toBase).obj = 1)

/- Example 4.32.4 (7): the ordinary categorical pullback and the pseudo-pullback formed in
`Cat/TwoArrowGroupoid` are not equivalent categories. -/
@[stacks 0H2D "the two pullback constructions are inequivalent"]
#check (notEquivalent :
  ¬ Nonempty
    (pointToBase ⊡ pointToBase ≌
      (PseudoPullback pointOverBase.toBase pointOverBase.toBase).obj))

end BasedCategory.PseudoPullback.TwoArrowCounterexample
end CategoryTheory
