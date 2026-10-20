module

public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Representability
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped CategoryTheory

universe uI vI uC vC

namespace CategoryTheory

variable {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
variable [IsCofiltered I] (M : I ⥤ C)

/- Lemma 4.22.10: the four standard representability formulations of essential constancy for a
cofiltered diagram are equivalent. -/
@[stacks 05PZ]
#check (IsCofiltered.IsEssentiallyConstant.tfae M :
  List.TFAE [
    IsCofiltered.IsEssentiallyConstant M,
    ∃ c : Cone M, IsIso c.comparison,
    ∃ c : LimitCone M, IsIso c.cone.comparison,
    ∃ (X : C) (p : CostructuredArrow M X),
      (colimit (M.op ⋙ uliftYoneda.{uI})).IsRepresentedBy
        ((colimit.ι (M.op ⋙ uliftYoneda.{uI}) (Opposite.op p.left)).app
          (Opposite.op (Opposite.op X)) (ULift.up p.hom.op))])

end CategoryTheory
