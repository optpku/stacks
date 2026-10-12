/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.GradedObject.Instances
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Integer shifts of graded objects

This leaf fixes the canonical unit translation on integer-graded objects.  It makes the shift
structure and its additivity available to generic shifted-Hom constructions without rebuilding
instances in source files.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory.GradedObject

universe w v u

variable (C : Type u) [Category.{v} C]

/-- Integer-graded objects carry the canonical shift obtained by translating degrees by `1`. -/
@[stacks 09MM]
instance integerHasShift : HasShift (GradedObject ℤ C) ℤ :=
  GradedObject.hasShift (1 : ℤ)

/-- Every canonical shift functor on integer-graded objects is additive. -/
@[stacks 09MM "additivity of integer graded-object shifts"]
instance integerShiftFunctorAdditive [Preadditive C] (n : ℤ) :
    (shiftFunctor (GradedObject ℤ C) n).Additive := sorry

/-- Every canonical shift functor on integer-graded objects is linear for the pointwise
`R`-linear structure. -/
@[stacks 09MM "linearity of integer graded-object shifts"]
instance integerShiftFunctorLinear {R : Type w} [Semiring R] [Preadditive C] [Linear R C]
    (n : ℤ) : Functor.Linear R (shiftFunctor (GradedObject ℤ C) n) := sorry

end CategoryTheory.GradedObject
