/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.DiagonalModels.Equivalence.Construction

/-!
# Properties of the concrete diagonal-model comparison

This file records equivalence properties derived from the explicit equivalence between the direct
diagonal model and the iterated categorical-pullback model.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

universe vC vS uC uS

namespace CategoryTheory.Limits

noncomputable section

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]
variable (G₁ G₂ : C ⥤ S)

namespace CategoricalPullback.DiagonalModel.comparison

/-- The canonical comparison between the two concrete models is an equivalence. -/
instance isEquivalence :
    (CategoricalPullback.DiagonalModel.comparison G₁ G₂).IsEquivalence := sorry

end CategoricalPullback.DiagonalModel.comparison

end

end CategoryTheory.Limits
