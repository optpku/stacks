/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Shift
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.14.11

Computing a pointwise derived value is an isomorphism-invariant, shift-stable object property.
The generic ReasLib owner also exposes direct transports so downstream applications need not
rebuild local instances around the class-valued computation condition.
-/

/- Lemma 13.14.11 (1): pointwise right-derived computation is invariant under shift. -/
@[stacks 05SY] #check @CategoryTheory.Functor.RightDerived.ComputesAt.iff_shift

/- Lemma 13.14.11 (2): pointwise left-derived computation is invariant under shift. -/
@[stacks 05SY] #check @CategoryTheory.Functor.LeftDerived.ComputesAt.iff_shift

#check @CategoryTheory.Functor.RightDerived.ComputesAt.closedUnderIso
#check @CategoryTheory.Functor.LeftDerived.ComputesAt.closedUnderIso
#check @CategoryTheory.Functor.RightDerived.ComputesAt.stableUnderShift
#check @CategoryTheory.Functor.LeftDerived.ComputesAt.stableUnderShift
