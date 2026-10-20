/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.GradedObject.Monoidal

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe u
namespace ModuleCat

/-- Tensoring modules on the right preserves the coproducts of a graded tensor product. -/
instance gradedHasGoodTensorLeft {R : Type u} [CommRing R]
    (X Y Z : GradedObject ℤ (ModuleCat R)) : GradedObject.HasGoodTensor₁₂Tensor X Y Z := by
  intro i j
  change PreservesColimit _ (tensorRight (Z j))
  exact preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight (Z j))

/-- Tensoring modules on the left preserves the coproducts of a graded tensor product. -/
instance gradedHasGoodTensorRight {R : Type u} [CommRing R]
    (X Y Z : GradedObject ℤ (ModuleCat R)) : GradedObject.HasGoodTensorTensor₂₃ X Y Z := by
  intro i j
  change PreservesColimit _ (tensorLeft (X i))
  infer_instance

/-- Tensoring modules preserves the coproducts used to compare four graded factors. -/
instance gradedHasTensorFourExt {R : Type u} [CommRing R]
    (W X Y Z : GradedObject ℤ (ModuleCat R)) : GradedObject.HasTensor₄ObjExt W X Y Z := by
  intro i j
  change PreservesColimit _ (tensorLeft (W i))
  infer_instance

end ModuleCat
