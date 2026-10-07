module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/- Lemma 26.19.5: a closed immersion is quasi-compact. -/
@[stacks 01K7] #check (inferInstance : QuasiCompact f)

end AlgebraicGeometry
