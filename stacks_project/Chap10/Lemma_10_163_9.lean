module

public import ReasLib.RingTheory.Smooth.Normal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.163.9

@stack 033C
-/

/- Lemma 10.163.9 [stacks 033C]: canonical recall that normality ascends along a smooth algebra
map. -/
@[stacks 033C]
#check @Algebra.Smooth.isNormalRing_of_normal
