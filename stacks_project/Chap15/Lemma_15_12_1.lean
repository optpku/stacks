module

public import ReasLib.RingTheory.Henselian.Pair.Category
import StacksCheckRecall

/-!
# Henselization of ring pairs

This file recalls the adjunction defining Henselization of commutative-ring pairs.

@stack 0A02
-/

@[expose] public section

-- Lemma 15.12.1: the inclusion of Henselian pairs into all pairs has a left adjoint.
@[stacks 0A02 "Lemma 15.12.1"]
#check @RingPairCat.henselianPairInclusion_isRightAdjoint

-- The shared owner also exposes the source and target categories and the chosen functorial model.
@[stacks 0A02 "category of ring pairs"]
#check @RingPairCat

@[stacks 0A02 "category of Henselian pairs"]
#check @RingPairCat.HenselianPairCat

@[stacks 0A02 "chosen pair Henselization"]
#check @RingPairCat.henselization

@[stacks 0A02 "universal Henselian-pair data"]
#check @RingPairCat.PairHenselizationData
