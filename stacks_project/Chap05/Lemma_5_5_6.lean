module

public import ReasLib.Topology.Bases.Quotient
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.5.6

The quotient realization of an open basis family is owned by
`ReasLib.Topology.Bases.Quotient`.
-/

/- Lemma 5.5.6: a family with the stated open and intersection properties is realized by
inverse-saturated open basis images of a continuous map. -/
@[stacks 0D5Q]
#check @TopologicalSpace.exists_continuousMap_with_openBasisImages
