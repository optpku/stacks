/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.MorphismProperty.Shift.InverseImage

@[expose] public section

/-!
# Triangulation Compatibility of Inverse-Image Morphism Properties

A triangulation-compatible morphism property pulls back along a full and faithful triangulated
functor.  Fullness lifts the missing component of a triangle morphism, while faithfulness reflects
the two remaining commutative squares.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.MorphismProperty.IsCompatibleWithTriangulation

open Limits Pretriangulated

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasZeroObject D]
  [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- the inverse image of a triangulation-compatible morphism property along a full
and faithful triangulated functor is triangulation-compatible. -/
@[stacks 0GSL "triangulation compatibility under inverse image"]
instance inverseImage (W : MorphismProperty D) (F : C ⥤ D)
    [W.IsCompatibleWithTriangulation] [W.RespectsIso]
    [F.CommShift ℤ] [F.IsTriangulated] [F.Full] [F.Faithful] :
    (W.inverseImage F).IsCompatibleWithTriangulation := sorry


end CategoryTheory.MorphismProperty.IsCompatibleWithTriangulation
