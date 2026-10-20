module

public import ReasLib.RingTheory.Flat.Locus.BaseChange
import StacksCheckRecall

/-!
# Base change with a closed subset of the algebra

Lemma 15.19.2 is the source-and-base closed-subset form of tensor-product flatness ascent.

@stack 05LR
-/

@[stacks 05LR "Lemma 15.19.2"]
#check @Ideal.FlatLocus.tensorTower_add

@[stacks 05LR "closed-subset flatness along a tensor-product tower"]
#check @Ideal.FlatLocus.tensorTower_of_map_le
