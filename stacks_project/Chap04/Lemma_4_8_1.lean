/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.RepresentablePresheaf.Pullback
import StacksCheckRecall

@[expose] public section

universe w v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {F G H : Cᵒᵖ ⥤ Type w}
variable (a : F ⟶ G) (b : H ⟶ G) (X : C)

/- Lemma 4.8.1: a pullback of set-valued presheaves is computed objectwise by the explicit
type-level pullback. -/
@[stacks 0022 "objectwise explicit fibre product of presheaves"]
#check (presheafPullbackObjIso a b X :
  (pullback a b).obj (Opposite.op X) ≅
    Types.PullbackObj (a.app (Opposite.op X)) (b.app (Opposite.op X)))
#check presheafPullbackObjIso.hom_fst
#check presheafPullbackObjIso.hom_snd
#check presheafPullbackObjIso.inv_fst
#check presheafPullbackObjIso.inv_snd

end CategoryTheory.Limits
