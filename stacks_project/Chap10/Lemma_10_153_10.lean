module

public import ReasLib.RingTheory.Henselian.KrullDimension
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.153.10

@stack 06RS

Zero-dimensional local rings are henselian.
-/

@[stacks 06RS "zero-dimensional local rings are henselian"]
#check @HenselianLocalRing.of_krullDimLE_zero
