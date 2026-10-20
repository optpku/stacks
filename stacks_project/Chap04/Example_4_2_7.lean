module

public import Mathlib.CategoryTheory.Groupoid.Discrete
import StacksCheckRecall

@[expose] public section
universe u

namespace CategoryTheory

variable (C : Type u)

/- The source needs concrete category and groupoid data on the set of objects, not merely a
Prop-valued discreteness condition. The verified owners `discreteCategory` and
`instGroupoidDiscrete` supply that data, while `discreteEquiv` bridges mathlib's intentional
`Discrete C` wrapper back to `C`. The plausible `Discrete.isDiscrete`,
`obj_ext_of_isDiscrete`, and `Discrete.instSubsingletonDiscreteHom` APIs expose derived
consequences but do not own the hom construction; `Groupoid.IsTotallyDisconnected` is weaker, and
`Subgroupoid.discrete` starts from an existing groupoid. Thus the recalls below introduce no
mathematical generalization: only the wrapper representation differs, canonically by
`discreteEquiv`. This keeps the concrete equality-based homs and inverse operation available for
downstream use. -/

/- Example 4.2.7 (1): the objects of the canonical discrete category `Discrete C` correspond
canonically to the elements of `C` via `discreteEquiv : Discrete C ≃ C`. -/
@[stacks 001A "objects of the discrete groupoid"]
#check (discreteEquiv (α := C) : Discrete C ≃ C)

/- Example 4.2.7 (2): `discreteCategory C` gives `Discrete C` its canonical category structure,
with `X ⟶ Y` defined as the lifted equality type `ULift (PLift (X.as = Y.as))`; hence it is empty
when the objects differ and contains only the identity when they agree. -/
@[stacks 001A "equality-only morphisms"]
#check (discreteCategory C : SmallCategory (Discrete C))

/- Example 4.2.7 (3): the canonical category `Discrete C` is a groupoid via
`instGroupoidDiscrete`. -/
@[stacks 001A "discrete groupoid structure"]
#check (instGroupoidDiscrete (C := C) : Groupoid.{u} (Discrete C))

end CategoryTheory
