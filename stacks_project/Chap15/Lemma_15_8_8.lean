module

public import ReasLib.RingTheory.FittingIdeal.LocallyFree
import StacksCheckRecall

/-!
# Fitting ideals and finite locally free modules

@stack 07ZD
-/

-- Lemma 15.8.8: finite local freeness of rank `r` is equivalent to the prescribed pattern of
-- vanishing and unit Fitting ideals.
@[stacks 07ZD "finite locally free modules detected by Fitting ideals"]
#check @FittingIdeal.finiteLocallyFreeOfRank_tfae
