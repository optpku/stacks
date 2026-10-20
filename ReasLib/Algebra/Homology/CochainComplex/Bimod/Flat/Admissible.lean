/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bimod.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-base goodness and admissible short exact sequences

The two fixed-base goodness conditions satisfy all three two-out-of-three implications for short
exact sequences which split after forgetting the differential but retain the coefficient action.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Bimod

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable [MonoidalCategory (CochainComplex C ℤ)]
variable [MonoidalCategory (GradedObject ℤ C)]
variable [(CochainComplex.forgetToGraded C).LaxMonoidal]
variable [Preadditive (CochainComplex C ℤ)]
variable [MonoidalPreadditive (CochainComplex C ℤ)]

variable {A : Mon (CochainComplex C ℤ)}

namespace IsGradedFlat

variable [HasCoequalizers (GradedObject ℤ C)]
variable [∀ X : GradedObject ℤ C,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : GradedObject ℤ C,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]

/-- In an admissible short exact sequence, graded flatness of the left and middle terms implies
graded flatness of the right term. -/
@[stacks 0FSA "graded flatness of an admissible quotient"]
theorem of_left_middle (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₁ : IsGradedFlat S.X₁) (h₂ : IsGradedFlat S.X₂) :
    IsGradedFlat S.X₃ := sorry

/-- In an admissible short exact sequence, graded flatness of the outer terms implies graded
flatness of the middle term. -/
@[stacks 0FSA "graded flatness of an admissible extension"]
theorem of_left_right (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₁ : IsGradedFlat S.X₁) (h₃ : IsGradedFlat S.X₃) :
    IsGradedFlat S.X₂ := sorry

/-- In an admissible short exact sequence, graded flatness of the middle and right terms implies
graded flatness of the left term. -/
@[stacks 0FSA "graded flatness of an admissible kernel"]
theorem of_middle_right (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₂ : IsGradedFlat S.X₂) (h₃ : IsGradedFlat S.X₃) :
    IsGradedFlat S.X₁ := sorry

end IsGradedFlat

namespace IsKFlat

variable [HasCoequalizers (CochainComplex C ℤ)]
variable [∀ X : CochainComplex C ℤ,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : CochainComplex C ℤ,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]

/-- In an admissible short exact sequence, relative K-flatness of the left and middle terms implies
relative K-flatness of the right term. -/
@[stacks 0FSA "relative K-flatness of an admissible quotient"]
theorem of_left_middle (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₁ : IsKFlat S.X₁) (h₂ : IsKFlat S.X₂) :
    IsKFlat S.X₃ := sorry

/-- In an admissible short exact sequence, relative K-flatness of the outer terms implies relative
K-flatness of the middle term. -/
@[stacks 0FSA "relative K-flatness of an admissible extension"]
theorem of_left_right (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₁ : IsKFlat S.X₁) (h₃ : IsKFlat S.X₃) :
    IsKFlat S.X₂ := sorry

/-- In an admissible short exact sequence, relative K-flatness of the middle and right terms implies
relative K-flatness of the left term. -/
@[stacks 0FSA "relative K-flatness of an admissible kernel"]
theorem of_middle_right (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₂ : IsKFlat S.X₂) (h₃ : IsKFlat S.X₃) :
    IsKFlat S.X₁ := sorry

end IsKFlat

namespace IsGoodAtBase

variable [HasCoequalizers (CochainComplex C ℤ)]
variable [∀ X : CochainComplex C ℤ,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : CochainComplex C ℤ,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]

variable [HasCoequalizers (GradedObject ℤ C)]
variable [∀ X : GradedObject ℤ C,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : GradedObject ℤ C,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]

/-- In an admissible short exact sequence, fixed-base goodness of the left and middle terms implies
fixed-base goodness of the right term. -/
@[stacks 0FSA "fixed-base goodness of an admissible quotient"]
theorem of_left_middle (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₁ : IsGoodAtBase S.X₁) (h₂ : IsGoodAtBase S.X₂) :
    IsGoodAtBase S.X₃ := sorry

/-- In an admissible short exact sequence, fixed-base goodness of the outer terms implies
fixed-base goodness of the middle term. -/
@[stacks 0FSA "fixed-base goodness of an admissible extension"]
theorem of_left_right (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₁ : IsGoodAtBase S.X₁) (h₃ : IsGoodAtBase S.X₃) :
    IsGoodAtBase S.X₂ := sorry

/-- In an admissible short exact sequence, fixed-base goodness of the middle and right terms implies
fixed-base goodness of the left term. -/
@[stacks 0FSA "fixed-base goodness of an admissible kernel"]
theorem of_middle_right (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₂ : IsGoodAtBase S.X₂) (h₃ : IsGoodAtBase S.X₃) :
    IsGoodAtBase S.X₁ := sorry

end IsGoodAtBase

end CategoryTheory.Bimod

end
