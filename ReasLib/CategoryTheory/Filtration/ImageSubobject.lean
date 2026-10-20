module

public import ReasLib.CategoryTheory.Filtration.Induced
public import ReasLib.CategoryTheory.Subobject.Image

/-!
# Image Subobject Helpers for Filtrations

Lemmas connecting image subobjects to quotient filtrations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasImages C]

namespace IndexedFiltration

variable [HasPullbacks C]
variable {I : Type*} [Preorder I] {X Y : C}

/-- The quotient filtration at stage `i` equals the image of the composite `F^i ↪ A → Y`. -/
theorem quotient_eq_image (F : IndexedFiltration I X) (g : X ⟶ Y) (i : I) :
    (F.quotient g).stage i = imageSubobject ((F.stage i).arrow ≫ g) := sorry

end IndexedFiltration

end CategoryTheory
