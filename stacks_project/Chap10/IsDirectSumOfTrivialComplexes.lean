module

public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.TrivialSum
import StacksCheckRecall

@[expose] public section

/-!
# Compatibility facade for trivial finite free sums

@stack 00MY

The representation-independent owner is
`FiniteFreeComplex.IsTrivialSum`.  In particular, its disk constructor uses
the canonical `ChainComplex.disk` rather than a coordinate presentation.
-/

@[stacks 00MY] #check @FiniteFreeComplex.IsTrivialSum
@[stacks 00MY] #check @FiniteFreeComplex.IsTrivialSum.single
@[stacks 00MY] #check @FiniteFreeComplex.IsTrivialSum.disk
@[stacks 00MY] #check @ChainComplex.trivialSums.coproduct
@[stacks 00MY] #check @ChainComplex.trivialSums.biprod
@[stacks 00MY] #check @ChainComplex.trivialSums.iso_iff
