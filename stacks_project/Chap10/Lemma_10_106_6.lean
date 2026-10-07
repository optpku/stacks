module

public import ReasLib.RingTheory.CohenMacaulay.Maximal.RegularLocalRing
import StacksCheckRecall

@[expose] public section

/-!
# Maximal Cohen--Macaulay modules over regular local rings

@stack 00NT
-/

/- Lemma 10.106.6: over a regular local ring, every maximal Cohen--Macaulay module
is free. -/
@[stacks 00NT]
#check @Module.MaximalCohenMacaulay.free_of_isRegularLocalRing
