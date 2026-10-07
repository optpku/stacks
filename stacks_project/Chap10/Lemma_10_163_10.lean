module

public import ReasLib.RingTheory.Smooth.Regularity.RegularBase
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.163.10

@stack 07NF
-/

/- Lemma 10.163.10 [stacks 07NF]: canonical recall that a smooth algebra over a regular ring is
regular. -/
@[stacks 07NF]
#check @Algebra.Smooth.isRegularRing_of_regular
