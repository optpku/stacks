module

import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Retracts
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.14.13 (05T0)

Assumptions as in Situation 13.14.1: `F` is an exact functor of triangulated categories and `S`
is a saturated multiplicative system compatible with the triangulation.  If `X ⊕ Y` computes
`RF`, then `X` and `Y` compute `RF`; similarly for `LF`.  No Karoubian hypothesis on the target
is involved.  The owners use the strong computation predicates
`Functor.RightDerived.ComputesAt` and `Functor.LeftDerived.ComputesAt`, which retain the
essential-constancy component rather than weak pointwise existence.
-/

open CategoryTheory

/- Lemma 13.14.13 (1)--(4): each summand of a computing binary biproduct computes the same
orientation of the derived value. -/
@[stacks 05T0 "(1)"] #check @CategoryTheory.Functor.RightDerived.ComputesAt.left_of_biprod
@[stacks 05T0 "(2)"] #check @CategoryTheory.Functor.RightDerived.ComputesAt.right_of_biprod
@[stacks 05T0 "(3)"] #check @CategoryTheory.Functor.LeftDerived.ComputesAt.left_of_biprod
@[stacks 05T0 "(4)"] #check @CategoryTheory.Functor.LeftDerived.ComputesAt.right_of_biprod

/- Convenient conjunction forms for downstream applications. -/
@[stacks 05T0 "right computation on both summands"]
#check @CategoryTheory.Functor.RightDerived.ComputesAt.of_biprod
@[stacks 05T0 "left computation on both summands"]
#check @CategoryTheory.Functor.LeftDerived.ComputesAt.of_biprod

/- Consequence: since retracts in a pretriangulated category are biproduct summands, the
computing objects are stable under retracts. -/
#check @CategoryTheory.Functor.RightDerived.ComputesAt.of_retract
#check @CategoryTheory.Functor.LeftDerived.ComputesAt.of_retract
#check @CategoryTheory.Functor.RightDerived.ComputesAt.stableUnderRetracts
#check @CategoryTheory.Functor.LeftDerived.ComputesAt.stableUnderRetracts
