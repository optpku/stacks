/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Strictification
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open scoped Bicategory

universe vC vS uC uAux

variable {C : Type uC} [Category.{vC} C]
variable {S : Type (max uC (max uAux vC))} [Category.{max vC vS} S]
variable (p : S ⥤ C) [Functor.IsFibered.InGroupoids p]

/- Lemma 4.37.3 (Stacks 02XY): every category fibred in groupoids is bicategorically equivalent
over the base to a split category fibred in groupoids, equivalently to one associated to a
contravariant groupoid-valued presheaf. The saturated same-owner theorem is the canonical formal
statement. -/
@[stacks 02XY]
#check (Functor.IsFibered.InGroupoids.Strictification.existsSplitModel.{vC, vS, uC, uAux} p :
  ∃ (Y : FiberedCategoryOver.Groupoids.{
      uC, vC, max uC (max uAux vC), max vC vS} C)
      (_ : FiberedCategoryOver.Groupoids.ofFunctor p ≌ Y),
    Functor.IsFibered.Split.InGroupoids Y.p)

end CategoryTheory
