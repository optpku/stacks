/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Naturality
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition comparison for full-subcategory restriction

Preservation of object properties composes, and restricting a composite
functor agrees canonically with composing the two restricted functors.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.ObjectProperty.FullSubcategory.restrict

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable {P : ObjectProperty C} {Q : ObjectProperty D}
variable {R : ObjectProperty E}

/-- Two composable functors carrying `P` into `Q` and `Q` into `R` have a
composite carrying `P` into `R`. -/
theorem mapsToComp {F : C ⥤ D} {G : D ⥤ E}
    (hF : P ≤ Q.inverseImage F) (hG : Q ≤ R.inverseImage G) :
    P ≤ R.inverseImage (F ⋙ G) := sorry

/-- Restriction of a composite is canonically isomorphic to the composite of
the restricted functors. -/
@[stacks 001D "composition comparison for full-subcategory restriction"]
def compIso (F : C ⥤ D) (G : D ⥤ E)
    (hF : P ≤ Q.inverseImage F) (hG : Q ≤ R.inverseImage G) :
    restrict (F ⋙ G) (mapsToComp hF hG) ≅
      restrict F hF ⋙ restrict G hG :=
  (R.fullyFaithfulι.whiskeringRight P.FullSubcategory).preimageIso
    (Iso.refl (P.ι ⋙ F ⋙ G))

/-- The forward composition comparison is componentwise the identity on
underlying objects. -/
@[simp]
theorem compIso_hom_app_hom (F : C ⥤ D) (G : D ⥤ E)
    (hF : P ≤ Q.inverseImage F) (hG : Q ≤ R.inverseImage G)
    (X : P.FullSubcategory) :
    ((compIso F G hF hG).hom.app X).hom =
      𝟙 (G.obj (F.obj X.obj)) := sorry

/-- The inverse composition comparison is componentwise the identity on
underlying objects. -/
@[simp]
theorem compIso_inv_app_hom (F : C ⥤ D) (G : D ⥤ E)
    (hF : P ≤ Q.inverseImage F) (hG : Q ≤ R.inverseImage G)
    (X : P.FullSubcategory) :
    ((compIso F G hF hG).inv.app X).hom =
      𝟙 (G.obj (F.obj X.obj)) := sorry

end CategoryTheory.ObjectProperty.FullSubcategory.restrict
