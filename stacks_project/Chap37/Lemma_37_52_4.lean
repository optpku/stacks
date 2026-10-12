/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ClosedPoint.Specialization
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.52.4: for a locally finite-type morphism and a specialization
`x ⤳ x′` with `x′` closed in its fibre, fibrewise closed points between them are
dense in the closure of `x` inside the fibre over `f x`. -/
@[stacks 053U] #check
  (AlgebraicGeometry.Scheme.Hom.closure_closedPoints_between_specializations :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x x' : X),
      Specializes x x' →
      f.asFiber x' ∈ closedPoints (f.fiber (f x')) →
      closure
          {x₁ : f.fiber (f x) |
            x₁ ∈ closedPoints (f.fiber (f x)) ∧
              Specializes (f.asFiber x) x₁ ∧
              Specializes (f.fiberι (f x) x₁) x'} =
        closure ({f.asFiber x} : Set (f.fiber (f x))))

end AlgebraicGeometry.Scheme.Hom
