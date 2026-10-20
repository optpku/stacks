/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Characterization.Left
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Properties
public import ReasLib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Vanishing Characterizations of Derived-Acyclic Objects

This umbrella exposes the left- and right-derived vanishing criteria.  The declarations below
own the right-derived half; the public left-derived dual is provided by `Characterization.Left`.
Bounded derived functors are integer indexed, while ordinary derived functors are naturally
indexed by `ℕ`.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

section BoundedBelowVanishes

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]

/-- Stacks 015C: all strictly positive bounded-below right-derived degrees of
`RF` vanish on `A`. -/
@[stacks 015C]
abbrev RightDerived.Bounded.Vanishes.aboveZero
    (RF : DerivedCategory.Plus 𝒜 ⥤ DerivedCategory.Plus ℬ) (A : 𝒜) : Prop :=
  ∀ ⦃i : ℤ⦄, 0 < i → IsZero ((Functor.RightDerived.degree RF i).obj A)

end BoundedBelowVanishes

section BoundedBelow

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]
  [(𝟭 𝒜).toBoundedBelowDerived.IsLocalization
    (HomotopyCategory.Plus.quasiIso 𝒜)]
  (RF : DerivedCategory.Plus 𝒜 ⥤ DerivedCategory.Plus ℬ)
  (α : F.toBoundedBelowDerived ⟶ DerivedCategory.Plus.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso 𝒜)]

/-- Stacks 015C: an object is bounded-below right acyclic precisely when its
degree-zero comparison is invertible and all positive derived degrees vanish. -/
@[stacks 015C]
theorem RightAcyclic.Bounded.iff_zero_and_vanishes
    (A : 𝒜) :
    RightAcyclic.Bounded F A ↔
      IsIso ((Functor.RightDerived.zero F RF α).app A) ∧
        RightDerived.Bounded.Vanishes.aboveZero RF A := sorry

/-- Stacks 015C: for a left exact additive functor, bounded-below right
acyclicity is precisely positive-degree derived vanishing. -/
@[stacks 015C]
theorem RightAcyclic.Bounded.iff_vanishes
    [PreservesFiniteLimits F] (A : 𝒜) :
    RightAcyclic.Bounded F A ↔
      RightDerived.Bounded.Vanishes.aboveZero RF A := sorry

end BoundedBelow

section RightDerivedVanishes

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive] [HasInjectiveResolutions 𝒜]

/-- Stacks 015C: all strictly positive ordinary right-derived degrees of `F`
vanish on `A`. -/
@[stacks 015C]
abbrev RightDerived.Vanishes.aboveZero (A : 𝒜) : Prop :=
  ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj A)

end RightDerivedVanishes

section Unbounded

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive] [HasInjectiveResolutions 𝒜]

/-- Stacks 015C: ordinary right acyclicity is characterized by its degree-zero
comparison and vanishing in all positive degrees. -/
@[stacks 015C]
theorem RightAcyclic.iff_zero_and_vanishes
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso 𝒜 (up ℤ))]
    (A : 𝒜) :
    RightAcyclic F A ↔
      IsIso (F.toRightDerivedZero.app A) ∧ RightDerived.Vanishes.aboveZero F A := sorry

/-- Stacks 015C: for a left exact additive functor, ordinary right acyclicity
is precisely positive-degree right-derived vanishing. -/
@[stacks 015C]
theorem RightAcyclic.iff_vanishes
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso 𝒜 (up ℤ))]
    [PreservesFiniteLimits F] (A : 𝒜) :
    RightAcyclic F A ↔ RightDerived.Vanishes.aboveZero F A := sorry

end Unbounded

end Functor

end CategoryTheory
