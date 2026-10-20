/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Presheaf.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor

universe u v u' v' u'' v'' w

/- Remark 96.19.1: the relative Čech complex `K^•(f, F)` is also defined for a presheaf,
although Sites, Section 7.45 does not define the pullback maps in that setting. For a
triangle `h ⋙ f ≅ g`, the pullback map is the composite of `f_*` applied to the unit of
the presheaf inverse-image/right-Kan-extension adjunction for `h` with the inverse of
the canonical pushforward comparison. This applies to Type-valued and abelian-valued
presheaves, and specializes to the functors between total categories of categories
fibred in groupoids; a strict triangle uses its canonical comparison isomorphism. -/
@[stacks 06X8] #check
  (CategoryTheory.Functor.presheafPullbackMap :
    ∀ {V : Type u} [Category.{v} V] {U : Type u'} [Category.{v'} U]
      {X : Type u''} [Category.{v''} X] {A : Type w} [Category A]
      (h : V ⥤ U) (f : U ⥤ X) {g : V ⥤ X} (e : h ⋙ f ≅ g)
      [∀ F : Vᵒᵖ ⥤ A, HasRightKanExtension h.op F]
      [∀ F : Uᵒᵖ ⥤ A, HasRightKanExtension f.op F]
      [∀ F : Vᵒᵖ ⥤ A, HasRightKanExtension g.op F],
      (f.op.ran : (Uᵒᵖ ⥤ A) ⥤ (Xᵒᵖ ⥤ A)) ⟶
        presheafInverseImage h A ⋙
          (g.op.ran : (Vᵒᵖ ⥤ A) ⥤ (Xᵒᵖ ⥤ A)))
