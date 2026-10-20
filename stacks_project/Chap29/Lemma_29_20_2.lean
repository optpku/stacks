module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ClosedPoint
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.20.2: an algebraic residue-field extension makes a point closed in its fibre. -/
@[stacks 01TE] #check
  (AlgebraicGeometry.asFiber_mem_closedPoints_of_isAlgebraic_residueField :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (x : X),
      Algebra.IsAlgebraic (S.residueField (f x)) (X.residueField x) →
        f.asFiber x ∈ closedPoints (f.fiber (f x)))

/- If the image point is also closed, then the original point is closed. -/
#check
  (AlgebraicGeometry.mem_closedPoints_of_isAlgebraic_residueField_of_image_mem_closedPoints :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (x : X),
      Algebra.IsAlgebraic (S.residueField (f x)) (X.residueField x) →
        f x ∈ closedPoints S → x ∈ closedPoints X)
