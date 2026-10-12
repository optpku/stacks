/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.GradedObject.Shift
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Category
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The shifted-Hom grading of integer-graded objects

This leaf specializes the generic shifted-Hom construction to the canonical unit translation on
integer-graded objects. Fixing the scalar ring to `ℤ` makes the grading canonical and suitable for
typeclass inference.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory.GradedObject.ShiftedHom

universe v u

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- The shifted-Hom category of integer-graded objects has its canonical integer grading. -/
@[stacks 09MM, reducible]
instance grading :
    GradedCategory ℤ (ShiftedHomCategory (GradedObject ℤ C)) ℤ :=
  ShiftedHomCategory.gradedCategory (GradedObject ℤ C) ℤ

end CategoryTheory.GradedObject.ShiftedHom
