module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

/- Lemma 26.20.2: universal closedness is universal specialization lifting together with the
canonical quasi-compactness condition. -/
@[stacks 01KC] #check universallyClosed_eq_universallySpecializing

end AlgebraicGeometry
