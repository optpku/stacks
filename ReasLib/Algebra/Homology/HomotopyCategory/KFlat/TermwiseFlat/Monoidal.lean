/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.Flat.Monoidal
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.Monoidal
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.TermwiseFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal good flat models

K-flat homotopy objects represented by termwise-flat complexes form a monoidal full
subcategory when flat objects are closed under the coproducts occurring in totalization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

universe u v

namespace CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C]
variable [MonoidalCategory.IsFlat.Coproducts C]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := C)]

/-- K-flat homotopy objects with flat terms contain the tensor unit and are closed under tensor
products. -/
@[stacks 07A4 "monoidal good flat models", instance]
theorem isMonoidal : (HomotopyCategory.KFlat.termwiseFlat C).IsMonoidal := sorry

end CategoryTheory.HomotopyCategory.KFlat.TermwiseFlat
