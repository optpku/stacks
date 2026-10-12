/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.FlatQuotient
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.16.1

@stack 0522

The source statement says that two ideals whose quotient modules are flat have the same
property for their intersection.  The predicate and its intersection theorem are generic ideal
APIs in `ReasLib.RingTheory.Ideal.FlatQuotient`; this chapter entry is deliberately only a
source-facing recall, so later chapters import the shared owner rather than this file.
-/

open Ideal

/- Lemma 15.16.1 (Stacks `0522`): flat quotient ideals are closed under intersections. -/
@[stacks 0522 "flat quotient ideals are closed under binary intersections"]
#check @Ideal.IsFlatQuotient.inf

/- The quotient-module action and predicate are the canonical reusable objects. -/
#check @Ideal.quotientSmulTopModule
#check @Ideal.IsFlatQuotient

end
