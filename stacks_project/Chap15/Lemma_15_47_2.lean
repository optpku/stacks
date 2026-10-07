module

public import ReasLib.RingTheory.Regular.JRing.Quotient
import StacksCheckRecall

/-!
# Lemma 15.47.2

@stack 07P8
-/

@[expose] public section

/-! # Lemma 15.47.2: the regular-point trace criterion for J-1 rings -/

/- Lemma 15.47.2, tag `07P8`: the regular-point trace criterion for `J-1`. -/
@[stacks 07P8 "regular-point trace criterion for J-1 rings"]
#check @IsJ1Ring.iff_regularPoint_zeroLocus
