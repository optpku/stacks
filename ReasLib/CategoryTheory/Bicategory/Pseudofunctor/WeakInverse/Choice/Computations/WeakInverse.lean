module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.WeakInverse.Choice.Equivalence

/-!
# Computations for the chosen weak-inverse package

This file identifies the two equivalences stored by `chosenWeakInverse`.
-/

@[expose] public section

universe wB vB uB wC vC uC

namespace CategoryTheory.Pseudofunctor

open scoped Bicategory

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable (F : B ⥤ᵖ C) [F.IsBiequivalence]

/-- The left equivalence stored in the chosen weak inverse is the explicit
source-side equivalence. -/
@[simp]
theorem chosenWeakInverse.left :
    (F.chosenWeakInverse).left = ChosenInverse.leftEquivalence F := sorry

/-- The right equivalence stored in the chosen weak inverse is the explicit
target-side equivalence. -/
@[simp]
theorem chosenWeakInverse.right :
    (F.chosenWeakInverse).right = ChosenInverse.rightEquivalence F := sorry

end CategoryTheory.Pseudofunctor
