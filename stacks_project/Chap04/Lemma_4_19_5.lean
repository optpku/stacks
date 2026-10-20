/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtered.ColimitComparisons
import StacksCheckRecall

@[expose] public section


open CategoryTheory

universe u v

namespace CategoryTheory.Limits

variable {I : Type u} [Category.{v} I]
variable (M : I ⥤ AddCommGrpCat.{max u v})
variable (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
variable (hI : Nonempty I)

/-
`colimit.post` is the canonical comparison from the colimit of the underlying sets to the
underlying set of the additive colimit. The verified filtered-colimit owner
`AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits` requires full `IsFiltered I` and
makes this comparison an isomorphism, while the local
`prodComparison.colim.surjective_of_commonSuccessors` is only a proof-side binary-product bridge.
The direct surjectivity statement therefore retains exactly the source's common-successor
condition. It also records `Nonempty I` explicitly: without it the empty category satisfies the
condition vacuously, but the comparison from the empty `Type`-colimit to the underlying singleton
of the zero abelian group is not surjective. This is the precise correction needed to recover the
source claim for nonempty index categories, and the canonical comparison map remains reusable in
later preservation arguments.
-/

/- Lemma 4.19.5: if the index category is nonempty and every pair of its objects admits a common
successor, then the canonical comparison map from the colimit of `M` in sets to the underlying set
of the colimit of `M` in abelian groups is surjective. -/
@[stacks 09WR "surjectivity of the set-to-abelian-group colimit comparison"]
#check (AddCommGrpCat.colimitComparison.surjective_of_commonSuccessors
    (M := M) hObj hI :
  Function.Surjective (AddCommGrpCat.colimitComparison M))

end CategoryTheory.Limits
