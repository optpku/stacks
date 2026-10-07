module

public import Mathlib.CategoryTheory.CommSq

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable {W X Y Z : C}

/-- The square `CommSq f g h i` commutes if and only if `f ≫ h = g ≫ i`. -/
theorem commSq_iff (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) :
    CommSq f g h i ↔ f ≫ h = g ≫ i := sorry

end CategoryTheory
