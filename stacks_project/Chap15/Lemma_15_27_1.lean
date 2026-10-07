module

public import ReasLib.RingTheory.AdicCompletion.DirectSum
import StacksCheckRecall

/-!
# The completed direct sum embeds universally into the product

@stack 05BC
-/

@[expose] public section

/- Lemma 15.27.1 (1): the canonical map from the completed direct sum to the product. -/
@[stacks 05BC "Lemma 15.27.1 (1)"]
#check @AdicCompletion.directSumToPi

/- Lemma 15.27.1 (2): this canonical map is universally injective over a complete
Noetherian ring. -/
@[stacks 05BC "Lemma 15.27.1 (2)"]
#check @AdicCompletion.directSumToPi_universallyInjective

#check @AdicCompletion.directSumToPi_of
#check @AdicCompletion.directSumToPi_comp_of
