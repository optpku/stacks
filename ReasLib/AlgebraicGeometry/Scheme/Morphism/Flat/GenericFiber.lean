module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Integrality from the generic fiber of a flat morphism

A flat morphism to an integral scheme has integral source whenever its fiber over the generic
point of the target is integral.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- If `f : X ⟶ Y` is flat, `Y` is integral, and the fiber of `f` over the generic point of `Y`
is integral, then `X` is integral. -/
@[stacks 0BCM]
theorem isIntegral_of_flat_of_genericFiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsIntegral Y]
    (hgeneric : IsIntegral (Scheme.Hom.fiber f (genericPoint Y))) :
    IsIntegral X := sorry

end AlgebraicGeometry.Scheme.Hom
