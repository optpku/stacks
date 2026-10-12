/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Retracts
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.14.13 (05T0)

This entry recalls the retract-stable object properties for the strong computation predicates
`Functor.RightDerived.ComputesAt` and `Functor.LeftDerived.ComputesAt`.  The neutral owner retains
the essential-constancy component; it does not silently replace it by weak pointwise existence.
The binary-biproduct conclusions are thin bridges over the generic object-property retract API.
-/

open CategoryTheory

/- The Karoubian retract-stability owners for the two computation predicates. -/
#check @CategoryTheory.Functor.RightDerived.ComputesAt.stableUnderRetracts
#check @CategoryTheory.Functor.LeftDerived.ComputesAt.stableUnderRetracts

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

/- Explicit retract transport is available when a direct summand is represented by a `Retract`.
-/
#check @CategoryTheory.Functor.RightDerived.ComputesAt.of_retract
#check @CategoryTheory.Functor.LeftDerived.ComputesAt.of_retract
