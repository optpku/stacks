module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Counterexample.NonQuasiCompactLocus

@[expose] public section

/- Example 16.2.6 (1): the smooth locus in the standard infinitely generated example is the
union of the basic opens `D(yᵢ)`. -/
@[stacks 07CB] #check @Algebra.SmoothCounterexample.smoothLocus_eq_iUnion_basicOpen

/- Example 16.2.6 (2): this smooth locus is not quasi-compact over a nontrivial coefficient
ring. -/
@[stacks 07CB] #check @Algebra.SmoothCounterexample.smoothLocus_not_isCompact
