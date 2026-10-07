module

public import ReasLib.AlgebraicGeometry.Scheme.Presheaf
import StacksCheckRecall

@[expose] public section

section

universe u

/- 71.11.1.1: The equation specifies the ambient type of F as a contravariant
set-valued functor on schemes, not a relative-Proj construction. -/
@[stacks 084A] #check (AlgebraicGeometry.Scheme.Presheaf.{u} : Type (u + 1))

end
