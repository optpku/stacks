module

public import stacks_project.Chap61.Lemma_61_5_7_AlongClosed
import StacksCheckRecall

@[expose] public section

open Algebra.WLocalHull

/- Lemma 61.5.7 (1): A → alongClosed A I is ind-Zariski. -/
@[stacks 0979] #check alongClosed_indZariski

/- Lemma 61.5.7 (2): Spec(alongClosed A I) is w-local. -/
@[stacks 0979] #check instWLocalSpace_alongClosed

/- Lemma 61.5.7 (3): the closed points of Spec(alongClosed A I) are V(IB). -/
@[stacks 0979] #check closedPoints_alongClosed

/- Lemma 61.5.7 (4): A ⧸ I ≅ alongClosed A I ⧸ IB via the canonical quotient map. -/
@[stacks 0979] #check bijective_quotientMap_alongClosed
