/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Basic
public import ReasLib.CategoryTheory.Comma.Over.Map

/-!
# Base change for canonical Hom-presheaves

This module records the pointwise forms of the canonical base-change
isomorphism for Hom-presheaves.  They are independent of a chosen fibred
category and are therefore stated for an arbitrary `Cat`-valued
pseudofunctor on an opposite locally discrete base.
-/

@[expose] public section

universe uC vC uP vP

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor

variable {C : Type uC} [Category.{vC} C]

/-- The forward component of `overMapCompPresheafHomIso` acts by precomposition with the inverse
composition constraint and postcomposition with the forward composition constraint. -/
theorem PresheafHom.BaseChange.Hom.app
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U V : C} {x y : F.obj (.mk (op U))}
    (q : V ⟶ U) (T : (Over V)ᵒᵖ)
    (α : (F.presheafHom x y).obj (op ((Over.map q).obj T.unop))) :
    ((F.overMapCompPresheafHomIso x y q).hom.app T) α =
      (F.mapComp'
          q.op.toLoc T.unop.hom.op.toLoc
          (q.op.toLoc ≫ T.unop.hom.op.toLoc) rfl).inv.toNatTrans.app x ≫
        α ≫
      (F.mapComp'
          q.op.toLoc T.unop.hom.op.toLoc
          (q.op.toLoc ≫ T.unop.hom.op.toLoc) rfl).hom.toNatTrans.app y := sorry

/-- The inverse component of `overMapCompPresheafHomIso` acts by precomposition with the forward
composition constraint and postcomposition with the inverse composition constraint. -/
theorem PresheafHom.BaseChange.Inv.app
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U V : C} {x y : F.obj (.mk (op U))}
    (q : V ⟶ U) (T : (Over V)ᵒᵖ)
    (α : (F.presheafHom
      ((F.map q.op.toLoc).toFunctor.obj x)
      ((F.map q.op.toLoc).toFunctor.obj y)).obj T) :
    ((F.overMapCompPresheafHomIso x y q).inv.app T) α =
      (F.mapComp'
          q.op.toLoc T.unop.hom.op.toLoc
          (q.op.toLoc ≫ T.unop.hom.op.toLoc) rfl).hom.toNatTrans.app x ≫
        α ≫
      (F.mapComp'
          q.op.toLoc T.unop.hom.op.toLoc
          (q.op.toLoc ≫ T.unop.hom.op.toLoc) rfl).inv.toNatTrans.app y := sorry

/-- At the identity object of the smaller slice, the inverse base-change comparison sends the
canonical identity-slice Hom section to its restriction along `Over.mapIdentityIso f`. -/
theorem PresheafHom.BaseChange.Inv.identitySlice
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U V : C} (f : V ⟶ U) {M N : F.obj (.mk (op U))}
    (φ : (F.map f.op.toLoc).toFunctor.obj M ⟶
      (F.map f.op.toLoc).toFunctor.obj N) :
    ((F.overMapCompPresheafHomIso M N f).inv.app (op (Over.mk (𝟙 V)))
        (F.presheafHomObjHomEquiv φ)) =
      (F.presheafHom M N).map (Over.mapIdentityIso f).hom.op φ := sorry

/-- At the identity object of the smaller slice, the forward base-change comparison cancels
restriction along `Over.mapIdentityIso f`. -/
theorem PresheafHom.BaseChange.Hom.identitySlice
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U V : C} (f : V ⟶ U) {M N : F.obj (.mk (op U))}
    (δ : (F.presheafHom M N).obj (op (Over.mk f))) :
    ((F.overMapCompPresheafHomIso M N f).hom.app (op (Over.mk (𝟙 V)))
        ((F.presheafHom M N).map (Over.mapIdentityIso f).hom.op δ)) =
      F.presheafHomObjHomEquiv δ := sorry

end Pseudofunctor

end CategoryTheory
