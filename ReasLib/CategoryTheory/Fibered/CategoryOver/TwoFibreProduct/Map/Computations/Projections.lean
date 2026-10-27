/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.TwoFibreProduct.Map.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection computations for two-fibre-product maps of fibred categories

This leaf exposes the component formulas and naturality equations for the canonical
projection comparisons of application-facing two-fibre-product maps.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.TwoFibreProduct

variable
  {X₁ Y₁ S₁ X₂ Y₂ S₂ :
    FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C}
  {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
  {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}

variable {ψ φ : CospanTransform F₁ G₁ F₂ G₂}

/-- Forgetting the forward first-projection comparison recovers the corresponding explicit
pseudo-pullback cell, up to its dependent endpoint transport. -/
theorem map.fstIso.hom (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    (map.fstIso ψ).hom.hom ≍
      (BasedCategory.PseudoPullback.map.fstIso
        (LocallyInduced.TwoFibreProduct.CospanTransform.forget ψ)).hom := by
  rfl

/-- Forgetting the inverse first-projection comparison recovers the inverse explicit
pseudo-pullback cell. -/
@[simp]
theorem map.fstIso.inv (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    (map.fstIso ψ).inv.hom =
      (BasedCategory.PseudoPullback.map.fstIso
        (LocallyInduced.TwoFibreProduct.CospanTransform.forget ψ)).inv := by
  rfl

/-- Forgetting the forward second-projection comparison recovers the corresponding explicit
pseudo-pullback cell, up to its dependent endpoint transport. -/
theorem map.sndIso.hom (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    (map.sndIso ψ).hom.hom ≍
      (BasedCategory.PseudoPullback.map.sndIso
        (LocallyInduced.TwoFibreProduct.CospanTransform.forget ψ)).hom := by
  rfl

/-- Forgetting the inverse second-projection comparison recovers the inverse explicit
pseudo-pullback cell. -/
@[simp]
theorem map.sndIso.inv (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    (map.sndIso ψ).inv.hom =
      (BasedCategory.PseudoPullback.map.sndIso
        (LocallyInduced.TwoFibreProduct.CospanTransform.forget ψ)).inv := by
  rfl

/-- The forward component of the natural first-projection comparison is the canonical
first-projection cell, up to its dependent endpoint transport. -/
theorem map.fstNatIso.hom.app (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    map.fstNatIso.hom.app ψ ≍ (map.fstIso ψ).hom := by
  rfl

/-- The inverse component of the natural first-projection comparison is the inverse canonical
first-projection cell. -/
@[simp]
theorem map.fstNatIso.inv.app (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    map.fstNatIso.inv.app ψ = (map.fstIso ψ).inv := by
  rfl

/-- The forward component of the natural second-projection comparison is the canonical
second-projection cell, up to its dependent endpoint transport. -/
theorem map.sndNatIso.hom.app (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    map.sndNatIso.hom.app ψ ≍ (map.sndIso ψ).hom := by
  rfl

/-- The inverse component of the natural second-projection comparison is the inverse canonical
second-projection cell. -/
@[simp]
theorem map.sndNatIso.inv.app (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    map.sndNatIso.inv.app ψ = (map.sndIso ψ).inv := by
  rfl

/-- The first-projection comparison is natural in a modification of cospan transformations. -/
theorem map₂.fstCommutes
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    map₂ Γ ▷
        _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.fst F₂ G₂ ≫
      (map.fstIso φ).hom ≍
        (map.fstIso ψ).hom ≫
          _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.fst F₁ G₁ ◁
            CospanTransform.Hom.left Γ := by
  apply heq_of_eq
  apply ObjectProperty.hom_ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext A
  change
    (CospanTransform.Hom.left Γ).hom.toNatTrans.app
        (BasedCategory.PseudoPullback.fstObj A) ≫ 𝟙 _ =
      𝟙 _ ≫ (CospanTransform.Hom.left Γ).hom.toNatTrans.app
        (BasedCategory.PseudoPullback.fstObj A)
  simp only [Category.comp_id, Category.id_comp]

/-- The second-projection comparison is natural in a modification of cospan transformations. -/
theorem map₂.sndCommutes
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    map₂ Γ ▷
        _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.snd F₂ G₂ ≫
      (map.sndIso φ).hom ≍
        (map.sndIso ψ).hom ≫
          _root_.CategoryTheory.FiberedCategoryOver.TwoFibreProduct.snd F₁ G₁ ◁
            CospanTransform.Hom.right Γ := by
  apply heq_of_eq
  apply ObjectProperty.hom_ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext A
  change
    (CospanTransform.Hom.right Γ).hom.toNatTrans.app
        (BasedCategory.PseudoPullback.sndObj A) ≫ 𝟙 _ =
      𝟙 _ ≫ (CospanTransform.Hom.right Γ).hom.toNatTrans.app
        (BasedCategory.PseudoPullback.sndObj A)
  simp only [Category.comp_id, Category.id_comp]

end FiberedCategoryOver.TwoFibreProduct

end CategoryTheory
