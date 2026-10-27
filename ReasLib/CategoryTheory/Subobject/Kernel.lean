/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Kernel Subobjects

This leaf collects pullback computations for kernel subobjects that are independent of a
particular exact-sequence or inverse-system presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasKernels C] [HasPullbacks C]

/-- The kernel subobject of a composite is the pullback of the kernel subobject of its second
factor along the first factor. -/
theorem kernelSubobject_comp_eq_pullback {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kernelSubobject (f ≫ g) = (Subobject.pullback f).obj (kernelSubobject g) := by
  apply le_antisymm
  · apply Subobject.le_of_factors
    rw [pullback_factors_iff, kernelSubobject_factors_iff, Category.assoc]
    exact kernelSubobject_arrow_comp (f ≫ g)
  · apply le_kernelSubobject
    rw [← Category.assoc, ← (Subobject.isPullback f (kernelSubobject g)).w,
      Category.assoc, kernelSubobject_arrow_comp, comp_zero]

end CategoryTheory.Limits
