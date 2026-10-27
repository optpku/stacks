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
    A.Factors f :=
  Subobject.factors_of_le f h
    (by simpa using imageSubobject_factors_comp_self f (𝟙 X))

/-- If a morphism does not factor through a subobject, then its image subobject is not contained
in that subobject. -/
theorem Subobject.not_imageSubobject_le_of_not_factors
    {X Y : C} (A : Subobject Y) (f : X ⟶ Y) (hf : ¬ A.Factors f) :
    ¬ imageSubobject f ≤ A :=
  fun h ↦ hf (Subobject.factors_of_imageSubobject_le f A h)

/-- In a balanced category with equalizers, the image subobject of an epimorphism is top. -/
theorem imageSubobject_eq_top_of_epi [HasEqualizers C] [Balanced C]
    {X Y : C} (f : X ⟶ Y) [Epi f] :
    imageSubobject f = (⊤ : Subobject Y) := by
  have hE : Epi (image.ι f) := epi_image_of_epi f
  exact Subobject.isIso_iff_mk_eq_top (image.ι f) |>.mp
    ((isIso_iff_mono_and_epi (image.ι f)).mpr ⟨inferInstance, hE⟩)

/-- The image subobject of a split epimorphism is top, without balancedness or equalizers. -/
theorem imageSubobject_eq_top_of_isSplitEpi
    {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] :
    imageSubobject f = (⊤ : Subobject Y) := by
  apply top_le_iff.mp
  apply Subobject.le_of_factors
  have hf : (imageSubobject f).Factors (𝟙 Y) := by
    simpa using imageSubobject_factors_comp_self f (section_ f)
  simpa using Subobject.factors_of_factors_right (⊤ : Subobject Y).arrow hf

/-- In a balanced category with equalizers, the image of a composite is the image of the second
map restricted to the image of the first. -/
theorem imageSubobject_comp_eq_imageSubobject_restriction [HasEqualizers C] [Balanced C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    imageSubobject (f ≫ g) = imageSubobject ((imageSubobject f).arrow ≫ g) := by
  have hE : Epi (factorThruImageSubobject f) := inferInstance
  have hI := (isIso_iff_mono_and_epi
    (image.preComp (factorThruImageSubobject f) ((imageSubobject f).arrow ≫ g))).mpr
      ⟨inferInstance, inferInstance⟩
  have hh := Subobject.mk_eq_mk_of_comm _ _
    (@asIso _ _ _ _
      (image.preComp (factorThruImageSubobject f) ((imageSubobject f).arrow ≫ g)) hI)
    (image.preComp_ι (factorThruImageSubobject f) ((imageSubobject f).arrow ≫ g))
  change imageSubobject (factorThruImageSubobject f ≫ (imageSubobject f).arrow ≫ g) = _ at hh
  simpa only [← Category.assoc, imageSubobject_arrow_comp] using hh

/-- Pushing an image subobject forward along a monomorphism identifies it with the image of the
composite. -/
theorem imageSubobject_comp_eq_map_of_mono [HasEqualizers C] [Balanced C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    imageSubobject (f ≫ g) = (Subobject.map g).obj (imageSubobject f) := by
  rw [imageSubobject_comp_eq_imageSubobject_restriction]
  rw [imageSubobject_mono, ← Subobject.map_mk, Subobject.mk_arrow]

/-- Precomposing by an epimorphism does not change an image subobject. -/
theorem imageSubobject_comp_eq_of_epi_left [HasEqualizers C] [Balanced C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] :
    imageSubobject (f ≫ g) = imageSubobject g := by
  have hI := (isIso_iff_mono_and_epi (image.preComp f g)).mpr
    ⟨inferInstance, inferInstance⟩
  exact Subobject.mk_eq_mk_of_comm _ _ (@asIso _ _ _ _ (image.preComp f g) hI)
    (image.preComp_ι f g)

/-- In an abelian category, a morphism whose image subobject is top is an epimorphism. -/
theorem epi_of_imageSubobject_eq_top [Abelian C]
    {X Y : C} (f : X ⟶ Y) (h : imageSubobject f = (⊤ : Subobject Y)) :
    Epi f := by
  have hI : IsIso (imageSubobject f).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).mpr h
  have hE : Epi (imageSubobject f).arrow :=
    (isIso_iff_mono_and_epi _).mp hI |>.2
  rw [← imageSubobject_arrow_comp f]
  exact epi_comp' inferInstance hE

end CategoryTheory.Limits
