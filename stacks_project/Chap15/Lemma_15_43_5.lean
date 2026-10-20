module

public import ReasLib.RingTheory.Completion.DiscreteValuationRing
import StacksCheckRecall

/-!
# Lemma 15.43.5 (0AP1)

@stack 0AP1
-/

@[expose] public section

/- Lemma 15.43.5 (0AP1): the discrete-valuation-ring property is preserved and reflected by
maximal-ideal completion. -/
@[stacks 0AP1]
#check @AdicCompletion.isDiscreteValuationRing_iff
