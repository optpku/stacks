module

public import stacks_project.Chap100.Definition_100_10_4_Structure
public import stacks_project.Chap100.Definition_100_10_4_Reduced
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
  (Z : Closeds (Points X))

/- Definition 100.10.4 (1): an algebraic stack structure on a closed subset `Z` of
`Points X` is a closed substack `Z'` of `X` with `Z'.pointsSet` equal to `Z`. -/
@[stacks 050C] #check ClosedSubstackStructure Z
#check ClosedSubstackStructure.ofSubstack
#check ClosedSubstackStructure.Y
#check ClosedSubstackStructure.ι
#check ClosedSubstackStructure.spec

/- Definition 100.10.4 (2): the reduced induced algebraic stack structure on `Z` is
the one constructed in Lemma 100.10.1. -/
@[stacks 050C] #check ClosedSubstackStructure.reduced Z
#check ClosedSubstackStructure.reduced_spec

/- Definition 100.10.4 (3): the reduction `X_red` of `X` is the reduced induced
algebraic stack structure on `Points X`. -/
@[stacks 050C] #check reduction
#check reductionι
#check reduction_spec

end AlgebraicGeometry.AlgebraicStack
