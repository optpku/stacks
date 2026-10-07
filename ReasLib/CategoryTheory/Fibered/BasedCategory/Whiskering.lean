module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso

/-!
# Universe-polymorphic whiskering for based natural isomorphisms

The bicategory-level whiskering operations require all based categories to inhabit one fixed
universe.  This file exposes the underlying based-functor operations directly, so the source,
intermediate, and target total categories may live in independent universes.
-/

@[expose] public section

namespace CategoryTheory

open BasedFunctor

universe u v uX vX uY vY uZ vZ

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {Z : BasedCategory.{vZ, uZ} C}

namespace BasedNatIso

/-- The forward and inverse left-whiskered based transformations satisfy the forward inverse
law.  The statement is universe-polymorphic in all three based categories. -/
theorem whiskerLeft.hom_inv_id
    (F : X ⥤ᵇ Y) {G H : Y ⥤ᵇ Z} (e : G ≅ H) :
    BasedCategory.whiskerLeft F e.hom ≫
        BasedCategory.whiskerLeft F e.inv = 𝟙 (F ⋙ G) := sorry

/-- The forward and inverse left-whiskered based transformations satisfy the inverse forward
law.  The statement is universe-polymorphic in all three based categories. -/
theorem whiskerLeft.inv_hom_id
    (F : X ⥤ᵇ Y) {G H : Y ⥤ᵇ Z} (e : G ≅ H) :
    BasedCategory.whiskerLeft F e.inv ≫
        BasedCategory.whiskerLeft F e.hom = 𝟙 (F ⋙ H) := sorry

/-- Left-whisker a based natural isomorphism without forcing the three based categories into a
common universe. -/
def whiskerLeft (F : X ⥤ᵇ Y) {G H : Y ⥤ᵇ Z} (e : G ≅ H) :
    F ⋙ G ≅ F ⋙ H where
  hom := BasedCategory.whiskerLeft F e.hom
  inv := BasedCategory.whiskerLeft F e.inv
  hom_inv_id := whiskerLeft.hom_inv_id F e
  inv_hom_id := whiskerLeft.inv_hom_id F e

/-- The forward transformation of universe-polymorphic left whiskering is the corresponding
left-whiskered based natural transformation. -/
@[simp]
theorem whiskerLeft.hom
    (F : X ⥤ᵇ Y) {G H : Y ⥤ᵇ Z} (e : G ≅ H) :
    (whiskerLeft F e).hom = BasedCategory.whiskerLeft F e.hom := sorry

/-- The inverse transformation of universe-polymorphic left whiskering is the corresponding
left-whiskered inverse based natural transformation. -/
@[simp]
theorem whiskerLeft.inv
    (F : X ⥤ᵇ Y) {G H : Y ⥤ᵇ Z} (e : G ≅ H) :
    (whiskerLeft F e).inv = BasedCategory.whiskerLeft F e.inv := sorry

/-- The forward and inverse right-whiskered based transformations satisfy the forward inverse
law.  The statement is universe-polymorphic in all three based categories. -/
theorem whiskerRight.hom_inv_id
    {F G : X ⥤ᵇ Y} (e : F ≅ G) (H : Y ⥤ᵇ Z) :
    BasedCategory.whiskerRight e.hom H ≫
        BasedCategory.whiskerRight e.inv H = 𝟙 (F ⋙ H) := sorry

/-- The forward and inverse right-whiskered based transformations satisfy the inverse forward
law.  The statement is universe-polymorphic in all three based categories. -/
theorem whiskerRight.inv_hom_id
    {F G : X ⥤ᵇ Y} (e : F ≅ G) (H : Y ⥤ᵇ Z) :
    BasedCategory.whiskerRight e.inv H ≫
        BasedCategory.whiskerRight e.hom H = 𝟙 (G ⋙ H) := sorry

/-- Right-whisker a based natural isomorphism without forcing the three based categories into a
common universe. -/
def whiskerRight {F G : X ⥤ᵇ Y} (e : F ≅ G) (H : Y ⥤ᵇ Z) :
    F ⋙ H ≅ G ⋙ H where
  hom := BasedCategory.whiskerRight e.hom H
  inv := BasedCategory.whiskerRight e.inv H
  hom_inv_id := whiskerRight.hom_inv_id e H
  inv_hom_id := whiskerRight.inv_hom_id e H

/-- The forward transformation of universe-polymorphic right whiskering is the corresponding
right-whiskered based natural transformation. -/
@[simp]
theorem whiskerRight.hom
    {F G : X ⥤ᵇ Y} (e : F ≅ G) (H : Y ⥤ᵇ Z) :
    (whiskerRight e H).hom = BasedCategory.whiskerRight e.hom H := sorry

/-- The inverse transformation of universe-polymorphic right whiskering is the corresponding
right-whiskered inverse based natural transformation. -/
@[simp]
theorem whiskerRight.inv
    {F G : X ⥤ᵇ Y} (e : F ≅ G) (H : Y ⥤ᵇ Z) :
    (whiskerRight e H).inv = BasedCategory.whiskerRight e.inv H := sorry

end BasedNatIso

end CategoryTheory
