module

public import ReasLib.RingTheory.DiscreteValuationRing.Completion
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.114.2 (09EJ)

@stack 09EJ
-/

/- Lemma 15.114.2, Stacks `09EJ`: finite separable extensions descend from the completed
fraction field of a discrete valuation ring. -/
@[stacks 09EJ "Lemma 15.114.2, descent of finite separable extensions from completion"]
#check @DVR.Completion.existsFiniteSeparableBaseChange
