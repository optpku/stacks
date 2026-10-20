/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasFiniteProducts C] [HasKernels C] [HasCokernels C]
variable [∀ {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f)]

/- Definition 12.5.1: the textbook definition is the canonical constructor for an abelian
category from finite products, kernels, cokernels, and invertible coimage-image comparisons. -/
@[stacks 0109] #check
  (Abelian.ofCoimageImageComparisonIsIso : Abelian C)

end CategoryTheory
