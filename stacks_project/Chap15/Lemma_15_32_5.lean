module

import StacksCheckRecall
public import ReasLib.RingTheory.Ideal.Regularity.Quotient

/-!
# Lemma 15.32.5

@stack 07CX
-/

@[expose] public section

/- Lemma 15.32.5, tag `07CX`: if `J / I` is an H1-regular ideal of `A / I`,
then `I ⊓ J ^ 2 = I * J`. -/
@[stacks 07CX "Lemma 15.32.5"]
#check @Ideal.IsH1RegularIdeal.inf_sq_eq_mul
