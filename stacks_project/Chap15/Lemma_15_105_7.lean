module

public import ReasLib.RingTheory.Etale.Weakly.Operations
import StacksCheckRecall

/-!
# Lemma 15.105.7

@stack 092H
-/

@[expose] public section

/- Lemma 15.105.7 (1): tensor-square multiplication flatness is preserved by base change. -/
@[stacks 092H "Lemma 15.105.7 (1)"]
#check @Algebra.TensorSquare.flat_baseChange

/- Lemma 15.105.7 (2): weakly etale maps are preserved by base change. -/
@[stacks 092H "Lemma 15.105.7 (2)"]
#check @Algebra.WeaklyEtale.baseChange
