module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

/- Definition 26.20.1: universally closed scheme morphisms are modeled by the canonical
`UniversallyClosed` morphism property. -/
@[stacks 01KB] #check UniversallyClosed
#check universallyClosed_iff

end AlgebraicGeometry
