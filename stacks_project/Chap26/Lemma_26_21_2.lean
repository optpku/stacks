module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/- Lemma 26.21.2: the diagonal of every scheme morphism is an immersion. -/
@[stacks 01KJ] #check (inferInstance : IsImmersion (pullback.diagonal f))

end AlgebraicGeometry
