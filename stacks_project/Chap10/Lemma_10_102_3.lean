module

public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.TrivialSum.LocalRing
import StacksCheckRecall

@[expose] public section

/-!
# Exact finite free complexes over a depth-zero local ring

@stack 00MY

The reusable statement is owned by `FiniteFreeComplex`; its exactness
hypothesis uses the owner's `ExactInPositiveDegrees` predicate.
-/

@[stacks 00MY]
#check @FiniteFreeComplex.isTrivialSum_of_exact_of_depth_zero
