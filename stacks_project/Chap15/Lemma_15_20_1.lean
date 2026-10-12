/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.FlatQuotient.ClosedFiber
import StacksCheckRecall

/-!
# Least ideal for closed-fiber flatness

Lemma 15.20.1 is the complete-local existence theorem for the canonical closed-fiber flat
quotient predicate.

@stack 0526
-/

@[stacks 0526 "Lemma 15.20.1"]
#check @Ideal.IsClosedFiberFlatQuotient.exists_isLeast

@[stacks 0526 "closed-fiber flat quotient ideal"]
#check @Ideal.IsClosedFiberFlatQuotient
