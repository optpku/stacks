/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Idempotents.Preadditive.Splitting
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

/- Lemma (0H9R). If `j ≫ q = 𝟙 Y` in a preadditive category, then
(1) `j` is a kernel of `𝟙 X - q ≫ j`, and
(2) `q` is a cokernel of `𝟙 X - q ≫ j`. -/
@[stacks 0H9R] #check
  (CategoryTheory.Idempotents.split_morphism_kernel_cokernel : ∀ {X Y : C} (j : Y ⟶ X) (q : X ⟶ Y)
    (hj : j ≫ q = 𝟙 Y),
    ∃ (hi : j ≫ (𝟙 X - q ≫ j) = 0) (hp : (𝟙 X - q ≫ j) ≫ q = 0),
      Nonempty (IsLimit (KernelFork.ofι j hi)) ∧
      Nonempty (IsColimit (CokernelCofork.ofπ q hp)))
