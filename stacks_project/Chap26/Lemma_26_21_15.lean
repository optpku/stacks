module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section Scheme

variable (X : Scheme.{u}) [IsAffine X]

/- Lemma 26.21.15 (1): an affine scheme is separated. -/
@[stacks 01KN] #check (inferInstance : X.IsSeparated)

end Scheme

section Morphism

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X]

/- Lemma 26.21.15 (2): a morphism with affine source is separated. -/
@[stacks 01KN] #check (inferInstance : IsSeparated f)

end Morphism
end AlgebraicGeometry
