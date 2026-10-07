module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree

/-!
# Fibre degrees of immersions

This file records the sharp uniform bound on the fibre degrees of an immersion.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The fibre degrees of an immersion are bounded by `1`. -/
theorem degreesOfFibresBoundedBy_one_of_isImmersion
    (f : X ⟶ Y) [IsImmersion f] :
    degreesOfFibresBoundedBy f 1 := sorry

/-- An immersion has universally bounded fibres, with uniform bound `1`. -/
theorem universallyBoundedFibres_of_isImmersion
    (f : X ⟶ Y) [IsImmersion f] :
    universallyBoundedFibres f :=
  ⟨1, degreesOfFibresBoundedBy_one_of_isImmersion f⟩

end Scheme.Hom
end AlgebraicGeometry
