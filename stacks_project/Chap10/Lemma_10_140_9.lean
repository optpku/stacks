module

public import ReasLib.RingTheory.Smooth.FractionRing
import StacksCheckRecall

/-!
# Lemma 10.140.9

@stack 07ND
-/

@[expose] public section

/- Lemma 10.140.9 [stacks 07ND]: canonical recall of the generic-point
fraction-field separability criterion. -/

@[stacks 07ND]
#check @FractionRing.isSmoothAt_bot_iff_isSeparable
