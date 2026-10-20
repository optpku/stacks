/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Products in low-degree sheaf cohomology

Objectwise cohomology preserves arbitrary products in degree zero, while its canonical product
comparison is injective in degree one.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe w v u

namespace CategoryTheory.Sheaf.Cohomology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)]
variable [HasProducts (Sheaf J AddCommGrpCat)]

/-- The canonical comparison from degree-zero cohomology of a product to the product of
degree-zero cohomology objects is invertible. -/
@[stacks 060L "degree-zero cohomology of a product", stacks 0D0A
  "Lemma 20.11.12: degree-zero product comparison"]
instance productComparison_isIso_zero
    (U : C) {I : Type w} (F : I → Sheaf J AddCommGrpCat) :
    IsIso
      (piComparison
        (Sheaf.cohomologyPresheafFunctor J 0 ⋙
          (evaluation Cᵒᵖ AddCommGrpCat).obj (op U)) F) := sorry

/-- The canonical comparison from degree-one cohomology of a product to the product of
degree-one cohomology objects is injective. -/
@[stacks 060L "degree-one cohomology of a product", stacks 0D0A
  "Lemma 20.11.12: degree-one product comparison"]
theorem productComparison_injective_one
    (U : C) {I : Type w} (F : I → Sheaf J AddCommGrpCat) :
    Function.Injective
      (piComparison
        (Sheaf.cohomologyPresheafFunctor J 1 ⋙
          (evaluation Cᵒᵖ AddCommGrpCat).obj (op U)) F) := sorry

end CategoryTheory.Sheaf.Cohomology
