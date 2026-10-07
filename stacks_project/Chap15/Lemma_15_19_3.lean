module

public import ReasLib.RingTheory.Flat.Locus.Descent
import StacksCheckRecall

/-!
# Descent with a closed subset of the algebra

Lemma 15.19.3 is the source-and-base closed-subset form of tensor-product flatness descent.

@stack 05LS
-/

@[stacks 05LS "Lemma 15.19.3"]
#check @Ideal.FlatLocus.tensorBaseChange_add_descends

@[stacks 05LS "closed-subset descent without the algebra ideal"]
#check @Ideal.FlatLocus.tensorBaseChange_descends
