module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.CommSq
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {E X' Z X : Scheme.{u}}
variable (e : E ⟶ X') (i : E ⟶ Z) (b : X' ⟶ X) (j : Z ⟶ X)

/- 59.106.0.1 (0EWM): the displayed diagram is a commutative square of schemes
   with objects `E`, `X'`, `Z`, and `X`, and right vertical morphism `b`. -/
@[stacks 0EWM]
#check (CategoryTheory.commSq_iff e i b j : CategoryTheory.CommSq e i b j ↔ e ≫ b = i ≫ j)
