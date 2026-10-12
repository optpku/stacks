/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Representability
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped CategoryTheory

universe uI vI uC vC

namespace CategoryTheory

variable {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
variable [IsFiltered I] (M : I ⥤ C)

/- Lemma 4.22.9: the four standard representability formulations of essential constancy for a
filtered diagram are equivalent. -/
@[stacks 05PY]
#check (IsFiltered.IsEssentiallyConstant.tfae M :
  List.TFAE [
    IsFiltered.IsEssentiallyConstant M,
    ∃ c : Cocone M, IsIso c.comparison,
    ∃ c : ColimitCocone M, IsIso c.cocone.comparison,
    ∃ (X : C) (p : StructuredArrow X M),
      (colimit (M ⋙ uliftYoneda.{uI})).IsRepresentedBy
        ((colimit.ι (M ⋙ uliftYoneda.{uI}) p.right).app
          (Opposite.op X) (ULift.up p.hom))])

end CategoryTheory
