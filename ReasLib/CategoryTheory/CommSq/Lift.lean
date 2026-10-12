/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Logic.IsEmpty.Basic

@[expose] public section

namespace CategoryTheory.CommSq

variable {C : Type*} [Category* C]
variable {W X Y Z : C} {f : W ⟶ X} {i : W ⟶ Y} {p : X ⟶ Z} {g : Y ⟶ Z}

/-- A commutative square has no lift if and only if its type of lift structures is empty. -/
theorem not_hasLift_iff_isEmpty (sq : CommSq f i p g) :
    ¬ sq.HasLift ↔ IsEmpty sq.LiftStruct := sorry

end CategoryTheory.CommSq
