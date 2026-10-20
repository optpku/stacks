/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Cech.Complex

/-! Compatibility checks for the covering-simplex Čech API. -/

open CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

universe u v w vS wA

variable {C : Type u} [Category.{v} C]
variable {U X : FiberedCategoryOver.Groupoids C}

#check (CategoryTheory.FiberedCategoryOver.Groupoids.Cech.complex :
  (f : U ⟶ X) → (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) → CochainComplex AddCommGrpCat ℕ)

#check (CategoryTheory.FiberedCategoryOver.Groupoids.Cech.complex_d :
  ∀ (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ),
    (Cech.complex f F).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (Cech.cosimplicial f F).δ i)
