module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Zero
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable (A : Type u) [CommRing A]

/- Example 27.8.14: for the standard grading on the one-variable polynomial ring `A[T]`, the
canonical morphism `Proj(A[T]) ⟶ Spec(A)` is an isomorphism. -/
@[stacks 01MI] #check
  (AlgebraicGeometry.ProjectiveSpace.toSpec_zero_isIso A :
    IsIso (AlgebraicGeometry.ProjectiveSpace.toSpec A 0))
