module

public import ReasLib.RingTheory.Smooth.Reduced
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.163.7

@stack 033B
-/

/- Lemma 10.163.7 [stacks 033B]: canonical recall that a smooth algebra over a
reduced ring is reduced. -/
@[stacks 033B]
#check @Algebra.Smooth.isReduced_of_reduced
