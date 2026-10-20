module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import StacksCheckRecall

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]

/- Lemma 29.36.12

An étale morphism is flat.
-/
@[stacks 02GS] #check
  (AlgebraicGeometry.instFlatOfSmooth (f := f) : AlgebraicGeometry.Flat f)

end AlgebraicGeometry
