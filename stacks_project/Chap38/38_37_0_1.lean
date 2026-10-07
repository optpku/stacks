module

import Mathlib.AlgebraicGeometry.Scheme
import ReasLib.CategoryTheory.CommSq
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

variable {E X' Z X : Scheme.{u}}
variable (top : E ⟶ X') (left : E ⟶ Z) (b : X' ⟶ X) (bottom : Z ⟶ X)

/- 38.37.0.1: The displayed square of schemes commutes. -/
@[stacks 0EV6] #check
  (CategoryTheory.commSq_iff top left b bottom :
    CategoryTheory.CommSq top left b bottom ↔ top ≫ b = left ≫ bottom)
