/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import ReasLib.CategoryTheory.MorphismProperty.Localization.Triangulated.DenominatorTriangle.Basic

/-!
# Rotation of triangle denominators

Rotation of triangles restricts to an equivalence of triangle-denominator categories.  The
construction is obtained from mathlib's generic equivalence of full subcategories, so its unit,
counit, and inverse remain those of the ambient under-category equivalence.
-/

@[expose] public section

open CategoryTheory.ObjectProperty CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.MorphismProperty.TriangleDenominator

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- If `W` respects isomorphisms, then the triangle-denominator object property is closed under
isomorphisms in the under-category. -/
instance objectProperty_isClosedUnderIsomorphisms (W : MorphismProperty C) [W.RespectsIso]
    (T : Triangle C) : (objectProperty W T).IsClosedUnderIsomorphisms := sorry

/-- Pulling the triangle-denominator property for `T.rotate` back along rotation gives the
triangle-denominator property for `T`. -/
theorem inverseImage_rotate (W : MorphismProperty C) [W.IsCompatibleWithShift ℤ]
    (T : Triangle C) :
    (objectProperty W T.rotate).inverseImage
        (Under.postEquiv T (triangleRotation C)).functor =
      objectProperty W T := sorry

/-- Rotation induces an equivalence between the triangle denominators under `T` and those under
`T.rotate`.  Only invariance under shifts and isomorphisms is required. -/
@[stacks 05R9 "rotation of triangle denominators"]
noncomputable def rotationEquivalence (W : MorphismProperty C) [W.RespectsIso]
    [W.IsCompatibleWithShift ℤ] (T : Triangle C) :
    TriangleDenominator W T ≌ TriangleDenominator W T.rotate :=
  (Under.postEquiv T (triangleRotation C)).congrFullSubcategory
    (P := objectProperty W T) (Q := objectProperty W T.rotate) (inverseImage_rotate W T)

/-- The rotation functor on triangle denominators. -/
noncomputable abbrev rotate (W : MorphismProperty C) [W.RespectsIso]
    [W.IsCompatibleWithShift ℤ] (T : Triangle C) :
    TriangleDenominator W T ⥤ TriangleDenominator W T.rotate :=
  (rotationEquivalence W T).functor

/-- The inverse-rotation functor on triangle denominators. -/
noncomputable abbrev invRotate (W : MorphismProperty C) [W.RespectsIso]
    [W.IsCompatibleWithShift ℤ] (T : Triangle C) :
    TriangleDenominator W T.rotate ⥤ TriangleDenominator W T :=
  (rotationEquivalence W T).inverse

/-- Rotation sends the target triangle of a denominator to its rotation. -/
@[simp]
theorem rotate_obj_right (W : MorphismProperty C) [W.RespectsIso]
    [W.IsCompatibleWithShift ℤ] (T : Triangle C) (U : TriangleDenominator W T) :
    ((rotate W T).obj U).obj.right = U.obj.right.rotate := sorry

/-- After rotating denominator triangles, the first projection is the original second
projection. -/
theorem rotate_comp_projection₁ (W : MorphismProperty C) [W.RespectsIso]
    [W.IsCompatibleWithShift ℤ] (T : Triangle C) :
    rotate W T ⋙ projection₁ W T.rotate = projection₂ W T := sorry

/-- After rotating denominator triangles, the second projection is the original third
projection. -/
theorem rotate_comp_projection₂ (W : MorphismProperty C) [W.RespectsIso]
    [W.IsCompatibleWithShift ℤ] (T : Triangle C) :
    rotate W T ⋙ projection₂ W T.rotate = projection₃ W T := sorry

end CategoryTheory.MorphismProperty.TriangleDenominator
