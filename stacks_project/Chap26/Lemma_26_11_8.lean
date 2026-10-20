module

public import Mathlib.AlgebraicGeometry.Limits
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [Finite X] [DiscreteTopology X]

/- Lemma 26.11.8: a scheme with finite discrete underlying space is affine. -/
@[stacks 02O0] #check (inferInstance : IsAffine X)

end AlgebraicGeometry.Scheme
