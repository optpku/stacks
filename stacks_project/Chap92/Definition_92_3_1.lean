module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Construction
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.CommRingCat.Under.PolynomialResolution
open Opposite
open Under
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe u

noncomputable section

variable (A : CommRingCat.{u}) (B : Under A) (n : ℕ)

/- Definition 92.3.1: Let A ⟶ B be a ring map. The standard resolution of B over A
is the augmentation ε : P_• ⟶ B with terms P_0 = A[B], P_1 = A[A[B]], … and maps as
constructed in Simplicial, Example 14.34.7. -/
@[stacks 08PM]
#check ((evaluation A).obj B : SimplicialObject.Augmented (Under A))

#check (evaluation.obj_eq A B n)
#check (evaluation A)
#check (functor A)
#check (face A)
#check (degeneracy A)
