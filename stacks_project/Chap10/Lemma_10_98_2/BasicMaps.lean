/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.InverseSystem
import StacksCheckRecall

@[expose] public section

/-!
# Positive Adic Quotient Maps

The former chapter-local quotient-factorization proof has been replaced by the
shared positive inverse-system API.

@stack 09B8
-/

@[stacks 09B8 "quotient of the inverse-limit projection"]
#check @CategoryTheory.PNatInverseSystem.limitProjectionQuotient

@[stacks 09B8 "quotient projection comparison"]
#check @CategoryTheory.PNatInverseSystem.limitProjectionQuotient_comp_mkQ
