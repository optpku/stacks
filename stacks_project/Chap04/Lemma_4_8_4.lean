/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.RepresentablePresheaf.RelativelyRepresentable
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] [HasPullbacks C]
variable (F : Cᵒᵖ ⥤ Type v)

/- Lemma 4.8.4: relative representability of a presheaf diagonal, relative representability of
all representable sections, and representability of all pairwise section pullbacks are
equivalent. -/
@[stacks 0024]
#check (Functor.relativelyRepresentable.diag_tfae F :
  [yoneda.relativelyRepresentable (diag F),
    ∀ (U : C) (ξ : yoneda.obj U ⟶ F), yoneda.relativelyRepresentable ξ,
    ∀ (U V : C) (ξ : yoneda.obj U ⟶ F) (ξ' : yoneda.obj V ⟶ F),
      (pullback ξ ξ').IsRepresentable].TFAE)

end CategoryTheory
