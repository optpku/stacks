module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.Koszul.Homology.First.BaseChange

/-!
# Lemma 15.31.3

@stack 063Q
-/

@[expose] public section

/-! # Lemma 15.31.3: first Koszul homology under tensor base change -/

/- Lemma 15.31.3, tag `063Q`: the canonical comparison from scalar extension of first Koszul
homology to the first homology of the base-changed family is surjective when the quotient is flat
over the base ring. -/
@[stacks 063Q "surjectivity of first Koszul homology under base change"]
#check @KoszulComplex.Homology.H1.BaseChange.map_surjective

#check @KoszulComplex.Homology.H1.BaseChange.map
#check @KoszulComplex.Homology.H1.BaseChange.map_epi
