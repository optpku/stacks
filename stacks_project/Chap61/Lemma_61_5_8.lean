module

public import stacks_project.Chap61.Lemma_61_5_8_AlongClosed
import StacksCheckRecall

@[expose] public section

open Algebra.WLocalHull

/- Lemma 61.5.8 (1): every point of V(IB) is a closed point of Spec(B). -/
@[stacks 097A] #check zeroLocus_map_subset_closedPoints

/- Lemma 61.5.8 (2): B → C is ind-Zariski, with C := alongClosed B (IB). -/
@[stacks 097A] #check alongClosed_indZariski

/- Lemma 61.5.8 (3): B ⧸ IB → C ⧸ IC is an isomorphism. -/
@[stacks 097A] #check bijective_quotientMap_alongClosed_map

/- Lemma 61.5.8 (4): Spec(C) is w-local. -/
@[stacks 097A] #check wLocalSpace_alongClosed_map

/- Lemma 61.5.8 (5): p : Spec(C) → Spec(A) is w-local. -/
@[stacks 097A] #check instIsWLocalMap_comap_alongClosed

/- Lemma 61.5.8 (6): p⁻¹(X_0) is the set of closed points of Spec(C). -/
@[stacks 097A] #check comap_preimage_closedPoints_alongClosed
