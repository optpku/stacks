/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Naturality
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Natural transformations between restricted functors

Ambient natural transformations and natural isomorphisms restrict to full
subcategories whenever their endpoint functors preserve the selected object
properties.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty.FullSubcategory.restrict

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {P : ObjectProperty C} {Q : ObjectProperty D}

/-- Restrict an ambient natural transformation to the selected full
subcategories. -/
@[stacks 001D "restriction of a natural transformation to full subcategories"]
def natTrans {F G : C ⥤ D}
    (hF : P ≤ Q.inverseImage F) (hG : P ≤ Q.inverseImage G)
    (α : F ⟶ G) : restrict F hF ⟶ restrict G hG :=
  (Q.fullyFaithfulι.whiskeringRight P.FullSubcategory).preimage
    (Functor.whiskerLeft P.ι α)

/-- The underlying component of a restricted natural transformation is the
corresponding ambient component. -/
@[simp]
theorem natTrans_app_hom {F G : C ⥤ D}
    (hF : P ≤ Q.inverseImage F) (hG : P ≤ Q.inverseImage G)
    (α : F ⟶ G) (X : P.FullSubcategory) :
    ((natTrans hF hG α).app X).hom = α.app X.obj := sorry

/-- Forgetting a restricted natural transformation recovers the ambient
transformation after the source inclusion. -/
theorem whiskerRight_natTrans {F G : C ⥤ D}
    (hF : P ≤ Q.inverseImage F) (hG : P ≤ Q.inverseImage G)
    (α : F ⟶ G) :
    Functor.whiskerRight (natTrans hF hG α) Q.ι =
      Functor.whiskerLeft P.ι α := sorry

/-- Restriction preserves identity natural transformations. -/
@[simp]
theorem natTrans_id (F : C ⥤ D) (hF : P ≤ Q.inverseImage F) :
    natTrans hF hF (𝟙 F) = 𝟙 (restrict F hF) := sorry

/-- Restriction preserves vertical composition of natural transformations. -/
@[simp]
theorem natTrans_comp {F G H : C ⥤ D}
    (hF : P ≤ Q.inverseImage F) (hG : P ≤ Q.inverseImage G)
    (hH : P ≤ Q.inverseImage H) (α : F ⟶ G) (β : G ⟶ H) :
    natTrans hF hH (α ≫ β) =
      natTrans hF hG α ≫ natTrans hG hH β := sorry

/-- Restrict an ambient natural isomorphism to the selected full
subcategories. -/
@[stacks 001D "restriction of a natural isomorphism to full subcategories"]
def natIso {F G : C ⥤ D}
    (hF : P ≤ Q.inverseImage F) (hG : P ≤ Q.inverseImage G)
    (e : F ≅ G) : restrict F hF ≅ restrict G hG :=
  (Q.fullyFaithfulι.whiskeringRight P.FullSubcategory).preimageIso
    (Functor.isoWhiskerLeft P.ι e)

/-- The underlying forward component of a restricted natural isomorphism is
the corresponding ambient component. -/
@[simp]
theorem natIso_hom_app_hom {F G : C ⥤ D}
    (hF : P ≤ Q.inverseImage F) (hG : P ≤ Q.inverseImage G)
    (e : F ≅ G) (X : P.FullSubcategory) :
    ((natIso hF hG e).hom.app X).hom = e.hom.app X.obj := sorry

/-- The underlying inverse component of a restricted natural isomorphism is
the corresponding ambient component. -/
@[simp]
theorem natIso_inv_app_hom {F G : C ⥤ D}
    (hF : P ≤ Q.inverseImage F) (hG : P ≤ Q.inverseImage G)
    (e : F ≅ G) (X : P.FullSubcategory) :
    ((natIso hF hG e).inv.app X).hom = e.inv.app X.obj := sorry

/-- The forward map of a restricted natural isomorphism is the restriction of
its forward ambient natural transformation. -/
@[simp]
theorem natIso_hom {F G : C ⥤ D}
    (hF : P ≤ Q.inverseImage F) (hG : P ≤ Q.inverseImage G)
    (e : F ≅ G) :
    (natIso hF hG e).hom = natTrans hF hG e.hom := sorry

/-- The inverse map of a restricted natural isomorphism is the restriction of
its inverse ambient natural transformation. -/
@[simp]
theorem natIso_inv {F G : C ⥤ D}
    (hF : P ≤ Q.inverseImage F) (hG : P ≤ Q.inverseImage G)
    (e : F ≅ G) :
    (natIso hF hG e).inv = natTrans hG hF e.inv := sorry

end CategoryTheory.ObjectProperty.FullSubcategory.restrict
