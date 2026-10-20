/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Object Properties on the Vertices of a Triangle

An object property on a category induces an object property on its category of triangles by
requiring the property at all three vertices.  This module exposes the three vertex projections
to the full subcategory and, for a shift-stable property, the canonical lift of such triangles to
triangles in the full subcategory.
-/

noncomputable section

universe v u

namespace CategoryTheory

open ObjectProperty Pretriangulated

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]

namespace ObjectProperty

/-- Stacks 0144: the object property on triangles whose three vertices satisfy `P`. -/
@[stacks 0144 "objectwise property on triangles"]
def triangle (P : ObjectProperty C) : ObjectProperty (Triangle C) :=
  P.inverseImage Triangle.π₁ ⊓
    (P.inverseImage Triangle.π₂ ⊓ P.inverseImage Triangle.π₃)

namespace triangle

variable (P : ObjectProperty C)

/-- Membership in `P.triangle` is membership in `P` at all three vertices. -/
@[simp, stacks 0144 "membership in the objectwise triangle property"]
theorem mem_iff (T : Triangle C) :
    P.triangle T ↔ P T.obj₁ ∧ P T.obj₂ ∧ P T.obj₃ := sorry

/-- An object of `P.triangle.FullSubcategory` satisfies `P` at its first vertex. -/
theorem obj₁_mem (T : P.triangle.FullSubcategory) : P T.obj.obj₁ := sorry

/-- An object of `P.triangle.FullSubcategory` satisfies `P` at its second vertex. -/
theorem obj₂_mem (T : P.triangle.FullSubcategory) : P T.obj.obj₂ := sorry

/-- An object of `P.triangle.FullSubcategory` satisfies `P` at its third vertex. -/
theorem obj₃_mem (T : P.triangle.FullSubcategory) : P T.obj.obj₃ := sorry

/-- The first-vertex projection from triangles satisfying `P` to `P.FullSubcategory`. -/
def π₁ : P.triangle.FullSubcategory ⥤ P.FullSubcategory :=
  P.lift (P.triangle.ι ⋙ Triangle.π₁) (obj₁_mem P)

/-- The second-vertex projection from triangles satisfying `P` to `P.FullSubcategory`. -/
def π₂ : P.triangle.FullSubcategory ⥤ P.FullSubcategory :=
  P.lift (P.triangle.ι ⋙ Triangle.π₂) (obj₂_mem P)

/-- The third-vertex projection from triangles satisfying `P` to `P.FullSubcategory`. -/
def π₃ : P.triangle.FullSubcategory ⥤ P.FullSubcategory :=
  P.lift (P.triangle.ι ⋙ Triangle.π₃) (obj₃_mem P)

/-- The underlying object of the first-vertex projection. -/
@[simp]
theorem π₁.obj (T : P.triangle.FullSubcategory) :
    ((π₁ P).obj T).obj = T.obj.obj₁ := sorry

/-- The underlying map of the first-vertex projection. -/
@[simp]
theorem π₁.map {T₁ T₂ : P.triangle.FullSubcategory} (f : T₁ ⟶ T₂) :
    ((π₁ P).map f).hom = f.hom.hom₁ := sorry

/-- The underlying object of the second-vertex projection. -/
@[simp]
theorem π₂.obj (T : P.triangle.FullSubcategory) :
    ((π₂ P).obj T).obj = T.obj.obj₂ := sorry

/-- The underlying map of the second-vertex projection. -/
@[simp]
theorem π₂.map {T₁ T₂ : P.triangle.FullSubcategory} (f : T₁ ⟶ T₂) :
    ((π₂ P).map f).hom = f.hom.hom₂ := sorry

/-- The underlying object of the third-vertex projection. -/
@[simp]
theorem π₃.obj (T : P.triangle.FullSubcategory) :
    ((π₃ P).obj T).obj = T.obj.obj₃ := sorry

/-- The underlying map of the third-vertex projection. -/
@[simp]
theorem π₃.map {T₁ T₂ : P.triangle.FullSubcategory} (f : T₁ ⟶ T₂) :
    ((π₃ P).map f).hom = f.hom.hom₃ := sorry

/-- The first edge at a triangle satisfying `P`, lifted to `P.FullSubcategory`. -/
def mor₁.app (T : P.triangle.FullSubcategory) : (π₁ P).obj T ⟶ (π₂ P).obj T :=
  ObjectProperty.homMk T.obj.mor₁

/-- The underlying first edge is the first edge of the ambient triangle. -/
@[simp]
theorem mor₁.app_hom (T : P.triangle.FullSubcategory) :
    (mor₁.app P T).hom = T.obj.mor₁ := sorry

/-- Naturality of the lifted first edge. -/
theorem mor₁.naturality {T₁ T₂ : P.triangle.FullSubcategory} (f : T₁ ⟶ T₂) :
    (π₁ P).map f ≫ mor₁.app P T₂ =
      mor₁.app P T₁ ≫ (π₂ P).map f := sorry

/-- The first edges form a natural transformation between the first two vertex projections. -/
def mor₁ : π₁ P ⟶ π₂ P where
  app := mor₁.app P
  naturality _ _ f := mor₁.naturality P f

/-- The second edge at a triangle satisfying `P`, lifted to `P.FullSubcategory`. -/
def mor₂.app (T : P.triangle.FullSubcategory) : (π₂ P).obj T ⟶ (π₃ P).obj T :=
  ObjectProperty.homMk T.obj.mor₂

/-- The underlying second edge is the second edge of the ambient triangle. -/
@[simp]
theorem mor₂.app_hom (T : P.triangle.FullSubcategory) :
    (mor₂.app P T).hom = T.obj.mor₂ := sorry

/-- Naturality of the lifted second edge. -/
theorem mor₂.naturality {T₁ T₂ : P.triangle.FullSubcategory} (f : T₁ ⟶ T₂) :
    (π₂ P).map f ≫ mor₂.app P T₂ =
      mor₂.app P T₁ ≫ (π₃ P).map f := sorry

/-- The second edges form a natural transformation between the last two vertex projections. -/
def mor₂ : π₂ P ⟶ π₃ P where
  app := mor₂.app P
  naturality _ _ f := mor₂.naturality P f

/-- The connecting edge at a triangle satisfying `P`, lifted through the shift comparison of the
full-subcategory inclusion. -/
noncomputable def mor₃.app [P.IsStableUnderShift ℤ]
    (T : P.triangle.FullSubcategory) :
    (π₃ P).obj T ⟶ ((π₁ P ⋙ shiftFunctor P.FullSubcategory (1 : ℤ)).obj T) :=
  ObjectProperty.homMk
    (T.obj.mor₃ ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app ((π₁ P).obj T))

/-- The underlying connecting edge is the ambient connecting edge followed by the inverse
inclusion-shift comparison. -/
@[simp]
theorem mor₃.app_hom [P.IsStableUnderShift ℤ]
    (T : P.triangle.FullSubcategory) :
    (mor₃.app P T).hom =
      T.obj.mor₃ ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app ((π₁ P).obj T) := sorry

/-- Naturality of the lifted connecting edge. -/
theorem mor₃.naturality [P.IsStableUnderShift ℤ]
    {T₁ T₂ : P.triangle.FullSubcategory} (f : T₁ ⟶ T₂) :
    (π₃ P).map f ≫ mor₃.app P T₂ =
      mor₃.app P T₁ ≫
        (π₁ P ⋙ shiftFunctor P.FullSubcategory (1 : ℤ)).map f := sorry

/-- The connecting edges form a natural transformation from the third vertex to the shifted
first vertex. -/
noncomputable def mor₃ [P.IsStableUnderShift ℤ] :
    π₃ P ⟶ π₁ P ⋙ shiftFunctor P.FullSubcategory (1 : ℤ) where
  app := mor₃.app P
  naturality _ _ f := mor₃.naturality P f

/-- Stacks 0144: triangles whose vertices satisfy a shift-stable property lift canonically to
triangles in the corresponding full subcategory. -/
@[stacks 0144 "lifting triangles to a full subcategory"]
noncomputable def lift [P.IsStableUnderShift ℤ] :
    P.triangle.FullSubcategory ⥤ Triangle P.FullSubcategory :=
  Triangle.functorMk (mor₁ P) (mor₂ P) (mor₃ P)

/-- The first object of the lifted triangle is the first-vertex projection. -/
@[simp]
theorem lift.obj₁ [P.IsStableUnderShift ℤ] (T : P.triangle.FullSubcategory) :
    ((lift P).obj T).obj₁ = (π₁ P).obj T := sorry

/-- The second object of the lifted triangle is the second-vertex projection. -/
@[simp]
theorem lift.obj₂ [P.IsStableUnderShift ℤ] (T : P.triangle.FullSubcategory) :
    ((lift P).obj T).obj₂ = (π₂ P).obj T := sorry

/-- The third object of the lifted triangle is the third-vertex projection. -/
@[simp]
theorem lift.obj₃ [P.IsStableUnderShift ℤ] (T : P.triangle.FullSubcategory) :
    ((lift P).obj T).obj₃ = (π₃ P).obj T := sorry

/-- The first morphism of the lifted triangle is the lifted first edge. -/
@[simp]
theorem lift.mor₁ [P.IsStableUnderShift ℤ] (T : P.triangle.FullSubcategory) :
    ((lift P).obj T).mor₁ = mor₁.app P T := sorry

/-- The second morphism of the lifted triangle is the lifted second edge. -/
@[simp]
theorem lift.mor₂ [P.IsStableUnderShift ℤ] (T : P.triangle.FullSubcategory) :
    ((lift P).obj T).mor₂ = mor₂.app P T := sorry

/-- The third morphism of the lifted triangle is the lifted connecting edge. -/
@[simp]
theorem lift.mor₃ [P.IsStableUnderShift ℤ] (T : P.triangle.FullSubcategory) :
    ((lift P).obj T).mor₃ = mor₃.app P T := sorry

/-- The first component of a map of lifted triangles is the first-vertex projection. -/
@[simp]
theorem lift.map_hom₁ [P.IsStableUnderShift ℤ]
    {T₁ T₂ : P.triangle.FullSubcategory} (f : T₁ ⟶ T₂) :
    ((lift P).map f).hom₁ = (π₁ P).map f := sorry

/-- The second component of a map of lifted triangles is the second-vertex projection. -/
@[simp]
theorem lift.map_hom₂ [P.IsStableUnderShift ℤ]
    {T₁ T₂ : P.triangle.FullSubcategory} (f : T₁ ⟶ T₂) :
    ((lift P).map f).hom₂ = (π₂ P).map f := sorry

/-- The third component of a map of lifted triangles is the third-vertex projection. -/
@[simp]
theorem lift.map_hom₃ [P.IsStableUnderShift ℤ]
    {T₁ T₂ : P.triangle.FullSubcategory} (f : T₁ ⟶ T₂) :
    ((lift P).map f).hom₃ = (π₃ P).map f := sorry

end triangle

end ObjectProperty

end CategoryTheory
