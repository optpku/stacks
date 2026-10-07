module

public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Lifting
import StacksCheckRecall

@[expose] public section

/- Equation 20.14.2.1: a map into a bounded-below injective resolution lifts strictly across a
termwise monomorphic quasi-isomorphism, giving the comparison morphism `β` in the resolution
square. -/
@[stacks 01FC]
#check @CochainComplex.InjectivePlus.exists_lift_of_termwiseMono

#check @CategoryTheory.CommSq
