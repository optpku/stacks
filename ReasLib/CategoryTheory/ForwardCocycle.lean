/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Basic

/-!
# Forward cocycle conditions

Nine morphisms in a category satisfy a forward cocycle condition when matching
source comparisons and one intermediate path force the remaining paths to agree.
-/

@[expose] public section

universe v w

namespace CategoryTheory

/-- Test-object form of a forward `C₂` cocycle in a category with explicit universes. -/
def forwardCocycleCondition {C : Type v} [Category.{w} C]
    {A₁ B₁ A₂ B₂ A₀ B₀ V₂ V₁ V₀ : C}
    (s₁ : A₁ ⟶ V₂) (t₁ : B₁ ⟶ V₀) (s₂ : A₂ ⟶ V₂) (t₂ : B₂ ⟶ V₁)
    (s₀ : A₀ ⟶ V₁) (t₀ : B₀ ⟶ V₀)
    (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂) (u₀ : A₀ ⟶ B₀) : Prop :=
  ∀ (W : C) (x₁ : W ⟶ A₁) (x₂ : W ⟶ A₂) (x₀ : W ⟶ A₀),
    x₁ ≫ s₁ = x₂ ≫ s₂ → x₂ ≫ u₂ ≫ t₂ = x₀ ≫ s₀ →
      x₁ ≫ u₁ ≫ t₁ = x₀ ≫ u₀ ≫ t₀

/-- `forwardCocycleCondition` is the test-object matching of the nine maps. -/
theorem forwardCocycleCondition_iff {C : Type v} [Category.{w} C]
    {A₁ B₁ A₂ B₂ A₀ B₀ V₂ V₁ V₀ : C}
    (s₁ : A₁ ⟶ V₂) (t₁ : B₁ ⟶ V₀) (s₂ : A₂ ⟶ V₂) (t₂ : B₂ ⟶ V₁)
    (s₀ : A₀ ⟶ V₁) (t₀ : B₀ ⟶ V₀)
    (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂) (u₀ : A₀ ⟶ B₀) :
    forwardCocycleCondition s₁ t₁ s₂ t₂ s₀ t₀ u₁ u₂ u₀ ↔
      ∀ (W : C) (x₁ : W ⟶ A₁) (x₂ : W ⟶ A₂) (x₀ : W ⟶ A₀),
        x₁ ≫ s₁ = x₂ ≫ s₂ → x₂ ≫ u₂ ≫ t₂ = x₀ ≫ s₀ →
          x₁ ≫ u₁ ≫ t₁ = x₀ ≫ u₀ ≫ t₀ :=
  sorry

end CategoryTheory
