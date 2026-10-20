module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ClosedPoint
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed points between specializations in scheme-theoretic fibres

For a locally finite-type morphism, fibrewise closed points lying between a point and a
specialization are dense in the closure of the original point in its fibre.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a locally finite-type morphism and a specialization `x ⤳ x'` with `x'` closed in its
fibre, the fibrewise closed points between them are dense in the closure of `x` inside its
fibre. -/
@[stacks 053U]
theorem closure_closedPoints_between_specializations
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x x' : X)
    (hxx' : Specializes x x')
    (hx'_closed : f.asFiber x' ∈ closedPoints (f.fiber (f x'))) :
    closure
        {x₁ : f.fiber (f x) |
          x₁ ∈ closedPoints (f.fiber (f x)) ∧
            Specializes (f.asFiber x) x₁ ∧
            Specializes (f.fiberι (f x) x₁) x'} =
      closure ({f.asFiber x} : Set (f.fiber (f x))) := sorry

end AlgebraicGeometry.Scheme.Hom
