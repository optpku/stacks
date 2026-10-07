module

public import ReasLib.CategoryTheory.Pretriangulated.K0.GrothendieckGroup
public import Mathlib.Algebra.Ring.NegOnePow

@[expose] public section

/-!
# Additivity in Triangulated Grothendieck Groups

This file records the standard object-class computations that follow from the
distinguished-triangle relations defining `TriangulatedK0`.
-/

open CategoryTheory.Limits
open scoped CategoryTheory
open scoped ZeroObject

universe v u

namespace CategoryTheory.TriangulatedK0

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- The zero object has zero class in the triangulated Grothendieck group. -/
@[simp]
theorem of_zero : of (0 : C) = 0 := sorry

/-- Isomorphic objects have the same class in the triangulated Grothendieck group. -/
theorem of_iso {X Y : C} (e : X ≅ Y) : of X = of Y := sorry

/-- Shifting an object by one negates its triangulated Grothendieck class. -/
@[simp]
theorem of_shift_one (X : C) : of (X⟦(1 : ℤ)⟧) = -of X := sorry

/-- Shifting an object by `n` multiplies its triangulated Grothendieck class by
the canonical sign `(-1)^n`. -/
theorem of_shift (X : C) (n : ℤ) : of (X⟦n⟧) = n.negOnePow • of X := sorry

/-- The class of a binary biproduct is the sum of the classes of its summands. -/
@[simp]
theorem of_biprod (X Y : C) : of (X ⊞ Y) = of X + of Y := sorry

end CategoryTheory.TriangulatedK0
