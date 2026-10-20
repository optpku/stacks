module

public import ReasLib.Algebra.Module.QuotSMulTop.FiniteLength
import StacksCheckRecall

/-!
# Finite Length of Principal Quotients in Dimension One

@stack 00PF
-/

@[expose] public section

/- Lemma 10.119.11: a nonzero principal quotient of a submodule in a
finite-dimensional fraction-field vector space has finite length when the
base ring has Krull dimension one. -/
@[stacks 00PF]
#check @QuotSMulTop.isFiniteLength_of_ringKrullDim_eq_one

@[stacks 00PF "bounded-dimension owner"]
#check @QuotSMulTop.isFiniteLength_of_nonzero
