/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.QuotientSection
import StacksCheckRecall

/-!
# 15.11.6.1

@stack 0EM1
-/

@[expose] public section

/- 15.11.6.1: an etale quotient section splits the quotient algebra with `A / I` as its first
factor. -/
@[stacks 0EM1 "quotient product decomposition from an etale section"]
#check @Algebra.Etale.exists_quotientProductEquiv_of_section
