/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Shift.ShiftedHom.Category
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u

variable (C : Type u) [Category.{v} C]
variable (R : Type w) [Ring R]
variable [Preadditive C] [Linear R C] [HasShift C ℤ]
variable [∀ n : ℤ, (shiftFunctor C n).Additive]
variable [∀ n : ℤ, Functor.Linear R (shiftFunctor C n)]

/- Remark 22.25.7 (09P3): for a preadditive `R`-linear category `C` with linear shifts by
`ℤ`, the category `Cᵍʳ` has the same objects as `C`, total morphisms given by the direct sum of
the shifted-Hom modules, and its canonical grading has degree-`n` part `ShiftedHom X Y n`. -/
@[stacks 09P3] #check
  (ShiftedHomCategory.gradedCategory C R :
    GradedCategory R (ShiftedHomCategory C) ℤ)

/- The total morphism module is the direct sum of all shifted-Hom modules. -/
#check @ShiftedHomCategory.homSpace

/- The degree-`n` summand is canonically the corresponding shifted-Hom module. -/
#check @ShiftedHomCategory.homDegreeEquivShiftedHom

/- Shifting the target translates the grading. -/
#check @ShiftedHomCategory.homDegreeShiftObjEquiv
