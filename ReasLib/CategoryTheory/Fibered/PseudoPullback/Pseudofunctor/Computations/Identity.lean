/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pseudofunctor.Construction.Action

/-!
# Pointwise identity comparison of the explicit pseudo-pullback pseudofunctor

Component formulas for the identity comparison and its inverse.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open Functor.IsHomLift
open CategoricalPullback
open scoped Bicategory

universe u v w vB

namespace CategoryTheory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

/-- The forward component of the bundled identity comparison is the bridge transport followed by
the explicit identity component. -/
@[simp]
theorem pseudofunctor.mapId.hom.app
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C))
    (P : (PseudoPullback S.fst S.snd).obj) :
    ((pseudofunctor C).mapId S).hom.toNatTrans.app P =
      (eqToIso (congrArg
        (fun theta : BasedCospanTransform S.fst S.snd S.fst S.snd =>
          _root_.CategoryTheory.BasedCategory.PseudoPullback.map theta)
        (Bicategory.Cospan.Hom.toBasedTransform.id S))).hom.toNatTrans.app P ≫
        (mapId.component S.fst S.snd P).hom := by
  rfl

/-- The inverse component of the bundled identity comparison is the inverse explicit component
followed by the inverse bridge transport. -/
@[simp]
theorem pseudofunctor.mapId.inv.app
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C))
    (P : (PseudoPullback S.fst S.snd).obj) :
    ((pseudofunctor C).mapId S).inv.toNatTrans.app P =
      (mapId.component S.fst S.snd P).inv ≫
        (eqToIso (congrArg
          (fun theta : BasedCospanTransform S.fst S.snd S.fst S.snd =>
            _root_.CategoryTheory.BasedCategory.PseudoPullback.map theta)
          (Bicategory.Cospan.Hom.toBasedTransform.id S))).inv.toNatTrans.app P := by
  rfl

/-- The base component of the forward bundled identity comparison is the identity. -/
@[simp]
theorem pseudofunctor.mapId.hom.app.base
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C))
    (P : (PseudoPullback S.fst S.snd).obj) :
    baseMap (((pseudofunctor C).mapId S).hom.toNatTrans.app P) =
      𝟙 (baseObj P) := by
  let h := congrArg
    _root_.CategoryTheory.BasedCategory.PseudoPullback.map
    (Bicategory.Cospan.Hom.toBasedTransform.id S)
  let E : (PseudoPullback S.fst S.snd ⟶ PseudoPullback S.fst S.snd) ⥤ C :=
    { obj := fun K => baseObj (K.obj P)
      map := fun η => baseMap (η.toNatTrans.app P)
      map_id := by intro K; rfl
      map_comp := by intros; rfl }
  change E.map (eqToHom h) ≫ 𝟙 _ = _
  refine (Category.comp_id _).trans ?_
  refine (eqToHom_map E h).trans ?_
  exact eqToHom_refl _ _

/-- The first component of the forward bundled identity comparison is the identity. -/
@[simp]
theorem pseudofunctor.mapId.hom.app.fst
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C))
    (P : (PseudoPullback S.fst S.snd).obj) :
    fstMap (((pseudofunctor C).mapId S).hom.toNatTrans.app P) =
      𝟙 (fstObj P) := by
  let h := congrArg
    _root_.CategoryTheory.BasedCategory.PseudoPullback.map
    (Bicategory.Cospan.Hom.toBasedTransform.id S)
  let E : (PseudoPullback S.fst S.snd ⟶ PseudoPullback S.fst S.snd) ⥤
      S.left.obj :=
    { obj := fun K => fstObj (K.obj P)
      map := fun η => fstMap (η.toNatTrans.app P)
      map_id := by intro K; rfl
      map_comp := by intros; rfl }
  change E.map (eqToHom h) ≫ 𝟙 _ = _
  refine (Category.comp_id _).trans ?_
  refine (eqToHom_map E h).trans ?_
  exact eqToHom_refl _ _

/-- The second component of the forward bundled identity comparison is the identity. -/
@[simp]
theorem pseudofunctor.mapId.hom.app.snd
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C))
    (P : (PseudoPullback S.fst S.snd).obj) :
    sndMap (((pseudofunctor C).mapId S).hom.toNatTrans.app P) =
      𝟙 (sndObj P) := by
  let h := congrArg
    _root_.CategoryTheory.BasedCategory.PseudoPullback.map
    (Bicategory.Cospan.Hom.toBasedTransform.id S)
  let E : (PseudoPullback S.fst S.snd ⟶ PseudoPullback S.fst S.snd) ⥤
      S.right.obj :=
    { obj := fun K => sndObj (K.obj P)
      map := fun η => sndMap (η.toNatTrans.app P)
      map_id := by intro K; rfl
      map_comp := by intros; rfl }
  change E.map (eqToHom h) ≫ 𝟙 _ = _
  refine (Category.comp_id _).trans ?_
  refine (eqToHom_map E h).trans ?_
  exact eqToHom_refl _ _

/-- The base component of the inverse bundled identity comparison is the identity. -/
@[simp]
theorem pseudofunctor.mapId.inv.app.base
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C))
    (P : (PseudoPullback S.fst S.snd).obj) :
    baseMap (((pseudofunctor C).mapId S).inv.toNatTrans.app P) =
      𝟙 (baseObj P) := by
  let h := congrArg
    _root_.CategoryTheory.BasedCategory.PseudoPullback.map
    (Bicategory.Cospan.Hom.toBasedTransform.id S)
  let E : (PseudoPullback S.fst S.snd ⟶ PseudoPullback S.fst S.snd) ⥤ C :=
    { obj := fun K => baseObj (K.obj P)
      map := fun η => baseMap (η.toNatTrans.app P)
      map_id := by intro K; rfl
      map_comp := by intros; rfl }
  change 𝟙 _ ≫ E.map (eqToHom h.symm) = _
  refine (Category.id_comp _).trans ?_
  refine (eqToHom_map E h.symm).trans ?_
  exact eqToHom_refl _ _

/-- The first component of the inverse bundled identity comparison is the identity. -/
@[simp]
theorem pseudofunctor.mapId.inv.app.fst
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C))
    (P : (PseudoPullback S.fst S.snd).obj) :
    fstMap (((pseudofunctor C).mapId S).inv.toNatTrans.app P) =
      𝟙 (fstObj P) := by
  let h := congrArg
    _root_.CategoryTheory.BasedCategory.PseudoPullback.map
    (Bicategory.Cospan.Hom.toBasedTransform.id S)
  let E : (PseudoPullback S.fst S.snd ⟶ PseudoPullback S.fst S.snd) ⥤
      S.left.obj :=
    { obj := fun K => fstObj (K.obj P)
      map := fun η => fstMap (η.toNatTrans.app P)
      map_id := by intro K; rfl
      map_comp := by intros; rfl }
  change 𝟙 _ ≫ E.map (eqToHom h.symm) = _
  refine (Category.id_comp _).trans ?_
  refine (eqToHom_map E h.symm).trans ?_
  exact eqToHom_refl _ _

/-- The second component of the inverse bundled identity comparison is the identity. -/
@[simp]
theorem pseudofunctor.mapId.inv.app.snd
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C))
    (P : (PseudoPullback S.fst S.snd).obj) :
    sndMap (((pseudofunctor C).mapId S).inv.toNatTrans.app P) =
      𝟙 (sndObj P) := by
  let h := congrArg
    _root_.CategoryTheory.BasedCategory.PseudoPullback.map
    (Bicategory.Cospan.Hom.toBasedTransform.id S)
  let E : (PseudoPullback S.fst S.snd ⟶ PseudoPullback S.fst S.snd) ⥤
      S.right.obj :=
    { obj := fun K => sndObj (K.obj P)
      map := fun η => sndMap (η.toNatTrans.app P)
      map_id := by intro K; rfl
      map_comp := by intros; rfl }
  change 𝟙 _ ≫ E.map (eqToHom h.symm) = _
  refine (Category.id_comp _).trans ?_
  refine (eqToHom_map E h.symm).trans ?_
  exact eqToHom_refl _ _

/-- Every forward packaged identity-comparison component of the explicit pseudo-pullback
pseudofunctor is vertical over the identity common-base map. -/
theorem pseudofunctor.mapId.hom.app.isHomLift
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C))
    (P : (PseudoPullback S.fst S.snd).obj) :
    (PseudoPullback S.fst S.snd).p.IsHomLift
      (𝟙 ((PseudoPullback S.fst S.snd).p.obj P))
      (((pseudofunctor C).mapId S).hom.toNatTrans.app P) := by
  infer_instance

/-- Every inverse packaged identity-comparison component of the explicit pseudo-pullback
pseudofunctor is vertical over the identity common-base map. -/
theorem pseudofunctor.mapId.inv.app.isHomLift
    (S : Bicategory.Cospan (BasedCategory.{max v vB, max w (max u (max v vB))} C))
    (P : (PseudoPullback S.fst S.snd).obj) :
    (PseudoPullback S.fst S.snd).p.IsHomLift
      (𝟙 ((PseudoPullback S.fst S.snd).p.obj P))
      (((pseudofunctor C).mapId S).inv.toNatTrans.app P) := by
  infer_instance

end

end PseudoPullback

end BasedCategory

end CategoryTheory
