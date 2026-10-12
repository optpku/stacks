/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor
public import ReasLib.CategoryTheory.Sites.Descent.PullHom

/-!
# Pullback of Hom morphisms for selected fiber pseudofunctors

This module records the total-category calculation obtained by postcomposing a
`pullHom` morphism for the selected fiber pseudofunctor with a selected
cartesian arrow.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Bicategory Opposite
open scoped CategoryTheory.Bicategory

namespace Functor

variable {C : Type u} [Category.{v} C]

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposing a normalized `pullHom` with a selected cartesian arrow gives the total
arrow obtained by first restricting the source object and then postcomposing the original
morphism.

This is the selected-cleavage calculation underlying restrictions of Hom-presheaf sections. -/
theorem FiberPseudofunctor.pullHom.postcompose.cartesian
    {T : Type uS} [Category.{vS} T] (p : T ⥤ C) [p.IsFibered]
    {X₁ X₂ Y Y' : C} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (k : Y' ⟶ Y)
    (kf₁ : Y' ⟶ X₁) (kf₂ : Y' ⟶ X₂)
    (hkf₁ : k ≫ f₁ = kf₁) (hkf₂ : k ≫ f₂ = kf₂)
    {M₁ : p.Fiber X₁} {M₂ : p.Fiber X₂}
    (φ : ((fiberPseudofunctor p).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((fiberPseudofunctor p).map f₂.op.toLoc).toFunctor.obj M₂) :
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := fiberPseudofunctor p) φ k kf₁ kf₂ hkf₁ hkf₂).1 ≫
      Chosen.cartesianHom p kf₂ M₂ =
    (((fiberPseudofunctor p).mapComp' f₁.op.toLoc k.op.toLoc kf₁.op.toLoc
        (opToLoc_comp_of_eq f₁ k kf₁ hkf₁)).hom.toNatTrans.app M₁).1 ≫
      Chosen.cartesianHom p k
        (((fiberPseudofunctor p).map f₁.op.toLoc).toFunctor.obj M₁) ≫
      φ.1 ≫ Chosen.cartesianHom p f₂ M₂ := sorry

/-- Pulling a morphism preceded by the unit comparison of the selected fiber pseudofunctor
removes that left unit shell. -/
theorem FiberPseudofunctor.pullHom.id.hom
    {T : Type uS} [Category.{vS} T] (p : T ⥤ C) [p.IsFibered]
    {U V W : C} {M : p.Fiber V}
    (a : V ⟶ U) (g : W ⟶ V) (b : W ⟶ U)
    (h_id : g ≫ 𝟙 V = g) (h_comp : g ≫ a = b) (N : p.Fiber U)
    (φ : M ⟶ ((fiberPseudofunctor p).map a.op.toLoc).toFunctor.obj N) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (((fiberPseudofunctor p).mapIdOp V).hom.toNatTrans.app M ≫ φ)
        g g b h_id h_comp =
      ((fiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ ≫
        ((fiberPseudofunctor p).mapComp' a.op.toLoc g.op.toLoc b.op.toLoc
          (opToLoc_comp_of_eq a g b h_comp)).inv.toNatTrans.app N := sorry

/-- Pulling a morphism followed by the inverse unit comparison of the selected fiber
pseudofunctor removes that right unit shell. -/
theorem FiberPseudofunctor.pullHom.id.inv
    {T : Type uS} [Category.{vS} T] (p : T ⥤ C) [p.IsFibered]
    {U V W : C} {M : p.Fiber V}
    (a : V ⟶ U) (g : W ⟶ V) (b : W ⟶ U)
    (h_comp : g ≫ a = b) (h_id : g ≫ 𝟙 V = g) (N : p.Fiber U)
    (φ : ((fiberPseudofunctor p).map a.op.toLoc).toFunctor.obj N ⟶ M) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (φ ≫ ((fiberPseudofunctor p).mapIdOp V).inv.toNatTrans.app M)
        g b g h_comp h_id =
      ((fiberPseudofunctor p).mapComp' a.op.toLoc g.op.toLoc b.op.toLoc
        (opToLoc_comp_of_eq a g b h_comp)).hom.toNatTrans.app N ≫
        ((fiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ := sorry

/-- A chosen cartesian arrow representing an identity restriction cancels the corresponding
forward composition comparison after reindexing along the other leg. -/
theorem FiberPseudofunctor.pullHom.comp.hom.mapCartesian
    {T : Type uS} [Category.{vS} T] (p : T ⥤ C) [p.IsFibered]
    {V W : C} (e : V ⟶ V) (g : W ⟶ V) (h_id : g ≫ e = g) (M : p.Fiber V)
    (φ : ((fiberPseudofunctor p).map e.op.toLoc).toFunctor.obj M ⟶ M)
    (hφ : φ.1 = (Cleavage.ofIsFibered p).cartesianHom e M) :
    ((fiberPseudofunctor p).mapComp' e.op.toLoc g.op.toLoc g.op.toLoc
        (opToLoc_comp_of_eq e g g h_id)).hom.toNatTrans.app M ≫
      ((fiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ =
    𝟙 _ := sorry

/-- Literal-composite form of `FiberPseudofunctor.pullHom.postcompose.cartesian`.

This is the standard restriction calculation when both normalized base arrows
are written as composites with `k`. -/
theorem FiberPseudofunctor.pullHom.postcompose.comp
    {T : Type uS} [Category.{vS} T] (p : T ⥤ C) [p.IsFibered]
    {X₁ X₂ Y Y' : C} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (k : Y' ⟶ Y)
    {M₁ : p.Fiber X₁} {M₂ : p.Fiber X₂}
    (φ : ((fiberPseudofunctor p).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((fiberPseudofunctor p).map f₂.op.toLoc).toFunctor.obj M₂) :
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := fiberPseudofunctor p) φ k (k ≫ f₁) (k ≫ f₂)).1 ≫
      Chosen.cartesianHom p (k ≫ f₂) M₂ =
    (((fiberPseudofunctor p).mapComp' f₁.op.toLoc k.op.toLoc (k ≫ f₁).op.toLoc
        (opToLoc_comp_of_eq f₁ k (k ≫ f₁) rfl)).hom.toNatTrans.app M₁).1 ≫
      Chosen.cartesianHom p k
        (((fiberPseudofunctor p).map f₁.op.toLoc).toFunctor.obj M₁) ≫
      φ.1 ≫ Chosen.cartesianHom p f₂ M₂ := sorry

/-- Reindexing a fiber morphism and then postcomposing with selected cartesian arrows agrees
with its normalized `pullHom`, after exposing the source composition comparison.

This is the companion normal form to
`FiberPseudofunctor.pullHom.postcompose.cartesian`; it is useful when a restriction is first
presented as the action of the selected fiber pseudofunctor. -/
theorem FiberPseudofunctor.pullHom.map.postcompose
    {T : Type uS} [Category.{vS} T] (p : T ⥤ C) [p.IsFibered]
    {X₁ X₂ Y Y' : C} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (g : Y' ⟶ Y)
    (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    {M₁ : p.Fiber X₁} {M₂ : p.Fiber X₂}
    (φ : ((fiberPseudofunctor p).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((fiberPseudofunctor p).map f₂.op.toLoc).toFunctor.obj M₂) :
    (((fiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ).1 ≫
      Chosen.cartesianHom p g
        (((fiberPseudofunctor p).map f₂.op.toLoc).toFunctor.obj M₂) ≫
      Chosen.cartesianHom p f₂ M₂ =
    (((fiberPseudofunctor p).mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (opToLoc_comp_of_eq f₁ g gf₁ hgf₁)).inv.toNatTrans.app M₁).1 ≫
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂).1 ≫
      Chosen.cartesianHom p gf₂ M₂ := sorry

end Functor

end CategoryTheory
