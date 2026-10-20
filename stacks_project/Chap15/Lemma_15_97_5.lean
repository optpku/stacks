module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.97.5

The finite-local-freeness and split-pair-map conclusions are owned directly by the integer-indexed
Berthelot-Ogus eta API, using the canonical divided-coordinate model.

@stack 0F7W
-/

-- Lemma 15.97.5 (1): the bounded finite-free eta term is finite locally free of the expected rank.
@[stacks 0F7W "(1) finite local freeness of eta terms"]
#check @CochainComplex.BerthelotOgus.Int.term_finiteLocallyFreeOfRank

-- Lemma 15.97.5 (2): the divided-coordinate pair map is a split monomorphism.
@[stacks 0F7W "(2) splitting of the divided-coordinate pair map"]
#check @CochainComplex.BerthelotOgus.Int.Pair.pairLinear_isSplitMono

-- Degreewise companions omit the irrelevant global boundedness and finite-free assumptions.
#check @CochainComplex.BerthelotOgus.Int.term_finiteLocallyFreeOfRank_of_isPrincipal
#check @CochainComplex.BerthelotOgus.Int.Pair.linear_isSplitMono
#check @CochainComplex.BerthelotOgus.Int.Pair.pairLinear_isSplitMono_of_isPrincipal
