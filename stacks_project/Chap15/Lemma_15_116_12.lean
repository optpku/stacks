module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.ArtinSchreier
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.116.12

The equicharacteristic degree-`p` weak-solution existence statement is owned by
`IsWeakSolutionFor.exists_of_degree_p_galois`.  This chapter file keeps the source label and the
literal intersection view while exposing the canonical stable-power object to downstream users.

@stack 09F1
-/

@[stacks 09F1 "Lemma 15.116.12: equicharacteristic degree-p weak solution"]
#check @IsWeakSolutionFor.exists_of_degree_p_galois

@[stacks 09F1 "Lemma 15.116.12: literal stable power intersection view"]
#check @IsWeakSolutionFor.exists_of_degree_p_galois_of_intersection

@[stacks 09F1 "Lemma 15.116.12: explicit composite-extension view"]
#check @IsWeakSolutionFor.exists_of_degree_p_galois_of_extension

#check @PerfectClosure.powerIntersection
#check @PerfectClosure.powerIntersection_eq
#check @DVR.Field.IsTotallyRamified
#check @IsWeakSolutionFor
