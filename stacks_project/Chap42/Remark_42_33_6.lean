/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.BivariantClass.Commutation

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.BivariantClass

universe u

/- Remark 42.33.6: Two bivariant classes commute when their two iterated cap actions agree
after every locally finite-type base change; equivalently, their two restricted composites
on the canonical fiber product agree. -/
@[stacks 0FA2] #check (AlgebraicGeometry.BivariantClass.Commute :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Z₁ Z₂ : Over S} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Z₁.hom] [LocallyOfFiniteType Z₂.hom]
    (f₁ : Z₁ ⟶ X) (f₂ : Z₂ ⟶ X)
    [LocallyOfFiniteType f₁.left] [LocallyOfFiniteType f₂.left]
    {p₁ p₂ : ℤ} (c₁ : BivariantClass delta f₁ p₁)
    (c₂ : BivariantClass delta f₂ p₂), Prop)

#check (AlgebraicGeometry.BivariantClass.commute_iff_comp :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Z₁ Z₂ : Over S} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Z₁.hom] [LocallyOfFiniteType Z₂.hom]
    (f₁ : Z₁ ⟶ X) (f₂ : Z₂ ⟶ X)
    [LocallyOfFiniteType f₁.left] [LocallyOfFiniteType f₂.left]
    {p₁ p₂ : ℤ} (c₁ : BivariantClass delta f₁ p₁)
    (c₂ : BivariantClass delta f₂ p₂),
    Commute delta f₁ f₂ c₁ c₂ ↔
      let P : Over S := ComponentRestriction.baseChange f₁ f₂
      -- Local instance justification (proof-local temporary data): the restricted composites require the canonical pullback to be locally of finite type over the base.
      letI := ComponentRestriction.locallyOfFiniteTypeBaseChange f₁ f₂
      let π₁ : P ⟶ Z₁ := ComponentRestriction.baseChangeToSource f₁ f₂
      let π₂ : P ⟶ Z₂ := ComponentRestriction.baseChangeToTarget f₁ f₂
      let square : IsPullback π₁.left π₂.left f₁.left f₂.left :=
        ComponentRestriction.baseChange_isPullback f₁ f₂
      let r₁ : BivariantClass delta π₂ p₁ := restrict delta π₁ π₂ f₂ square p₁ c₁
      let r₂ : BivariantClass delta π₁ p₂ := restrict delta π₂ π₁ f₁ square.flip p₂ c₂
      let d₁ : BivariantClass delta (π₂ ≫ f₂) (p₁ + p₂) := comp delta π₂ f₂ r₁ c₂
      let d₂ : BivariantClass delta (π₁ ≫ f₁) (p₂ + p₁) := comp delta π₁ f₁ r₂ c₁
      HEq d₁ d₂)
