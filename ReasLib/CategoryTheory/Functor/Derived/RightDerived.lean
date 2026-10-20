/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Degree-Zero Properties of Right Derived Functors

The APIs in this leaf concern the ordinary right derived functor of an
additive functor between abelian categories with injective resolutions.  They
are independent of a bounded-below model and belong to the generic
derived-functor hierarchy.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive] [HasInjectiveResolutions 𝒜]

/-- Stacks 05TD: the zero-th ordinary right derived functor is left exact. -/
@[stacks 05TD]
theorem rightDerivedZero_preservesFiniteLimits :
    PreservesFiniteLimits (F.rightDerived 0) := sorry

/-- Stacks 05TD: the ordinary degree-zero comparison is invertible exactly
when the original additive functor is left exact. -/
@[stacks 05TD]
theorem isIso_toRightDerivedZero_iff_preservesFiniteLimits :
    IsIso F.toRightDerivedZero ↔ PreservesFiniteLimits F := sorry

end Functor

end CategoryTheory
