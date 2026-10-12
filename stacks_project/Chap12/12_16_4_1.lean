/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.GradedObject
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Equiv
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (A B : GradedObjectWithShift (1 : ℤ) C) (k : ℤ)

/- 12.16.4.1: moving a shift from the target to the source changes its sign.  This is the
graded-object specialization of the shared equivalence for every category with an additive-group
shift. -/
@[stacks 09MH] #check
  (CategoryTheory.ShiftedHom.sourceShiftEquiv A B k : (A ⟶ B⟦k⟧) ≃ (A⟦-k⟧ ⟶ B))

end CategoryTheory
