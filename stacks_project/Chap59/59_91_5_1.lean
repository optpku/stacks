/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.CommSq
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {X' X Y' Y : Scheme.{u}}
variable (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/- 59.91.5.1 (0A29): the displayed base-change diagram is a commutative
   square of schemes with arrows `g'`, `f'`, `f`, and `g`. -/
@[stacks 0A29]
#check (CategoryTheory.commSq_iff g' f' f g :
  CategoryTheory.CommSq g' f' f g ↔ g' ≫ f = f' ≫ g)
