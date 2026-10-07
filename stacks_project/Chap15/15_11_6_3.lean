module

public import ReasLib.RingTheory.Etale.QuotientSection
import StacksCheckRecall

/-!
# 15.11.6.3

@stack 0EM3
-/

@[expose] public section

/- 15.11.6.3: the reduction of the integral closure has a quotient factor identified with the
base quotient. -/
@[stacks 0EM3 "integral-closure quotient factor"]
#check @Algebra.Etale.exists_integralClosureQuotientEquiv_of_section
