/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Strictification

import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open scoped Bicategory

universe vC vS uC uAux

variable {C : Type uC} [Category.{vC} C]
variable {S : Type (max uC (max vC uAux))} [Category.{max vC vS} S]
variable (p : S ⥤ C) [p.IsFibered]

/- Lemma 4.36.4: every fibred category over `C` is bicategorically equivalent over `C` to a
split fibred category, equivalently to the co-Grothendieck category of a contravariant strict
`Cat`-valued functor. The saturated same-owner theorem is the canonical formal statement. -/
@[stacks 004A]
#check (Functor.IsFibered.Strictification.existsSplitModel.{vC, vS, uC, uAux} p :
  ∃ (Y : FiberedCategoryOver.{
      uC, vC, max uC (max vC uAux), max vC vS} C)
      (_ : FiberedCategoryOver.ofFunctor p ≌ Y),
    Functor.IsFibered.Split Y.p)

end CategoryTheory
