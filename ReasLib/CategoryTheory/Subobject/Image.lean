/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Image Subobject Calculus

Generic image-subobject computations used by filtrations, exact sequences, and inverse systems.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasImages C]

/-- A morphism factors through a subobject whenever its image subobject is contained in that
subobject. -/
theorem Subobject.factors_of_imageSubobject_le
    {X Y : C} (f : X ⟶ Y) (A : Subobject Y) (h : imageSubobject f ≤ A) :
    A.Factors f := sorry

/-- If a morphism does not factor through a subobject, then its image subobject is not contained
in that subobject. -/
theorem Subobject.not_imageSubobject_le_of_not_factors
    {X Y : C} (A : Subobject Y) (f : X ⟶ Y) (hf : ¬ A.Factors f) :
    ¬ imageSubobject f ≤ A := sorry

/-- In a balanced category with equalizers, the image subobject of an epimorphism is top. -/
theorem imageSubobject_eq_top_of_epi [HasEqualizers C] [Balanced C]
    {X Y : C} (f : X ⟶ Y) [Epi f] :
    imageSubobject f = (⊤ : Subobject Y) := sorry

/-- The image subobject of a split epimorphism is top, without balancedness or equalizers. -/
theorem imageSubobject_eq_top_of_isSplitEpi
    {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] :
    imageSubobject f = (⊤ : Subobject Y) := sorry

/-- In a balanced category with equalizers, the image of a composite is the image of the second
map restricted to the image of the first. -/
theorem imageSubobject_comp_eq_imageSubobject_restriction [HasEqualizers C] [Balanced C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    imageSubobject (f ≫ g) = imageSubobject ((imageSubobject f).arrow ≫ g) := sorry

/-- Pushing an image subobject forward along a monomorphism identifies it with the image of the
composite. -/
theorem imageSubobject_comp_eq_map_of_mono [HasEqualizers C] [Balanced C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    imageSubobject (f ≫ g) = (Subobject.map g).obj (imageSubobject f) := sorry

/-- Precomposing by an epimorphism does not change an image subobject. -/
theorem imageSubobject_comp_eq_of_epi_left [HasEqualizers C] [Balanced C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] :
    imageSubobject (f ≫ g) = imageSubobject g := sorry

/-- In an abelian category, a morphism whose image subobject is top is an epimorphism. -/
theorem epi_of_imageSubobject_eq_top [Abelian C]
    {X Y : C} (f : X ⟶ Y) (h : imageSubobject f = (⊤ : Subobject Y)) :
    Epi f := sorry

end CategoryTheory.Limits
