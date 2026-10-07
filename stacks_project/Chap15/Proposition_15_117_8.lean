module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.EssentiallyFiniteType
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 15.117.8

The existence theorem for a solution of an essentially finite-type extension of discrete
valuation rings is owned by `IsSolutionFor.exists_of_essFiniteType`. This chapter file is a thin
source recall, so downstream users can import the ReasLib theorem without the proof-specific
p-basis, Epp, and integral-closure infrastructure.

@stack 09II
-/

/- Proposition 15.117.8: an essentially finite-type DVR extension admits a finite solution. -/
@[stacks 09II "Proposition 15.117.8: existence of a solution for an essentially finite-type DVR extension"]
#check @IsSolutionFor.exists_of_essFiniteType

#check @IsSolutionFor

end
