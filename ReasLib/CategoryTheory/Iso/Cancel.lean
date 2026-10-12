/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Iso

/-!
# Isomorphism cancellation simp lemmas

Common patterns in category-theoretic proofs involve cancelling `iso.hom ≫ iso.inv` or
`iso.inv ≫ iso.hom` pairs embedded in longer composites. These lemmas make `simp` handle
the most frequent cases automatically.
-/

@[expose] public section

namespace CategoryTheory

variable {D : Type*} [Category D]

namespace Iso

/-- Two consecutive iso pairs cancel after any incoming morphism. -/
@[simp]
theorem twoIsoTail_cancel {W X Y Z : D}
    (f : W ⟶ X) (i : X ≅ Y) (j : Y ≅ Z) :
    f ≫ i.hom ≫ j.hom ≫ j.inv ≫ i.inv = f := by
  simp [Category.assoc]

/-- Two consecutive iso pairs cancel before any outgoing morphism. -/
@[simp]
theorem twoIsoHead_cancel {W X Y Z : D}
    (i : X ≅ Y) (j : Y ≅ Z) (f : X ⟶ W) :
    i.hom ≫ j.hom ≫ j.inv ≫ i.inv ≫ f = f := by
  simp [Category.assoc]

/-- Conjugation by an iso pair on the left cancels. -/
@[simp]
theorem hom_inv_comp {X Y Z : D} (i : X ≅ Y) (f : X ⟶ Z) :
    i.hom ≫ i.inv ≫ f = f := by
  simp

/-- Conjugation by an iso pair on the right cancels. -/
@[simp]
theorem comp_hom_inv {X Y Z : D} (i : Y ≅ Z) (f : X ⟶ Y) :
    f ≫ i.hom ≫ i.inv = f := by
  simp [Category.assoc]

/-- An iso sandwich `i.hom ≫ f ≫ j.hom` can be moved past `j.inv`. -/
theorem sandwich_inv_cancel {W X Y Z : D}
    (i : W ≅ X) (f : X ⟶ Y) (j : Y ≅ Z) :
    (i.hom ≫ f ≫ j.hom) ≫ j.inv = i.hom ≫ f := by
  simp [Category.assoc]

/-- An iso sandwich: `i.inv` cancels `i.hom` on the left, `j.inv` cancels `j.hom` on the right. -/
theorem sandwich_cancel {W X Y Z : D}
    (i : W ≅ X) (f : X ⟶ Y) (j : Y ≅ Z) :
    i.inv ≫ (i.hom ≫ f ≫ j.hom) ≫ j.inv = f := by
  simp [Category.assoc]

end Iso

end CategoryTheory
