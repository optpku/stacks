/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree

/-!
# Fibre degrees under composition

This file records multiplicative bounds for fibre degrees under composition of
scheme morphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {n m : ℕ}

/-- If the fibre degrees of two composable scheme morphisms are bounded, then the fibre degrees
of their composite are bounded by the product of the two bounds. -/
theorem degreesOfFibresBoundedBy_comp
    (hf : degreesOfFibresBoundedBy f n) (hg : degreesOfFibresBoundedBy g m) :
    degreesOfFibresBoundedBy (f ≫ g) (n * m) := sorry

/-- The composite of two scheme morphisms with universally bounded fibres has universally
bounded fibres. -/
theorem universallyBoundedFibres_comp
    (hf : universallyBoundedFibres f) (hg : universallyBoundedFibres g) :
    universallyBoundedFibres (f ≫ g) := sorry

end Scheme.Hom
end AlgebraicGeometry
