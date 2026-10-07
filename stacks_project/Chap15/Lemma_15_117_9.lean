module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.EssentiallyFiniteType
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.117.9

The source theorem, including its explicit Nagata disjunction, is owned by
`IsSolutionFor.exists_separable_of_essFiniteType`. The target-Nagata specialization is exposed by
the same ReasLib leaf for applications that already carry `[NagataRing B]`.

@stack 0BRP
-/

/- Lemma 15.117.9: an essentially finite-type separable DVR extension satisfying the source
Nagata disjunction admits a separable solution. -/
@[stacks 0BRP "Lemma 15.117.9: existence of a separable solution under the Nagata hypothesis"]
#check @IsSolutionFor.exists_separable_of_essFiniteType

#check @IsSolutionFor.exists_separable_of_essFiniteType_of_target
#check @IsSeparableSolutionFor

end
