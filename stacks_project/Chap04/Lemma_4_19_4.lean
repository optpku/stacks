/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtered.ColimitComparisons
public import ReasLib.CategoryTheory.Filtered.ColimitComparisons.Counterexamples
import StacksCheckRecall

@[expose] public section


open CategoryTheory

universe w v u

noncomputable section

namespace CategoryTheory.Limits

variable {I : Type u} [Category.{v} I] [Small.{w} I]
variable (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
variable (M N : I ⥤ Type w)

/- Lemma 4.19.4 (1): if every pair of objects in the index category admits a common successor,
then the canonical comparison map
`colimit (M ⨯ N) ⟶ colimit M × colimit N`
is surjective for `Type`-valued diagrams `M` and `N`. -/
@[stacks 09WQ "surjectivity under common successors"]
#check (prodComparison.colim.surjective_of_commonSuccessors hObj M N :
  Function.Surjective (prodComparison colim M N))

/- Lemma 4.19.4 (2): even if every pair of objects in the index category admits a common
successor, colimits of `Type`-valued diagrams do not in general commute with finite nonempty
products; in fact, there is already a counterexample for binary products. -/
@[stacks 09WQ "binary-product counterexample"]
#check (prodComparison.colim.exists_not_bijective :
  ∃ (J : Type u) (_ : Category.{v} J) (_ : Small.{w} J)
    (_ : ∀ i j : J, ∃ k : J, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (F G : J ⥤ Type w),
      ¬ Function.Bijective (prodComparison colim F G))

end CategoryTheory.Limits
