module

public import Mathlib.AlgebraicGeometry.Properties
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/- Lemma 26.11.4: the underlying space of a scheme is locally quasi-compact. -/
@[stacks 01IV] #check (inferInstance : LocallyCompactSpace X)

end AlgebraicGeometry.Scheme
