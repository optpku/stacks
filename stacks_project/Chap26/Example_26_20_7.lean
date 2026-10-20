module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.UniversallyClosed
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveLine

section Source

variable (k : Type u) [Field k]

/- Example 26.20.7: the structure morphism of `ℙ¹_k` satisfies existence in the valuative
criterion and is universally closed. -/
@[stacks 01KG] #check
  UniversallyClosed.valuativeCriterion (ProjectiveSpace.toSpec k 1)
@[stacks 01KG] #check
  (inferInstance : QuasiCompact (ProjectiveSpace.toSpec k 1))
@[stacks 01KG] #check
  (inferInstance : UniversallyClosed (ProjectiveSpace.toSpec k 1))

end Source

section Generalization

variable (R : Type u) [CommRing R]

#check UniversallyClosed.valuativeCriterion (ProjectiveSpace.toSpec R 1)
#check (inferInstance : QuasiCompact (ProjectiveSpace.toSpec R 1))
#check (inferInstance : UniversallyClosed (ProjectiveSpace.toSpec R 1))

end Generalization

end AlgebraicGeometry.ProjectiveLine
