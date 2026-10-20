/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.AlgebraicGeometry.GroupoidsOver.ObstructionTheory

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The obstruction-module functors `O_x` have injective countable product
comparisons: `O_x(∏ᶜ M) ⟶ ∏ᶜ O_x(M n)` is injective. -/
def ObstructionTheory.natPiComparison_injective {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S}
    (𝒪 : ObstructionTheory X) : Prop :=
  ∀ (ξ : ObjectOverSpec X) (M : ℕ → ModuleCat.{u} ξ.carrier),
    Function.Injective (piComparison (𝒪.module ξ) M).hom

/-- `natPiComparison_injective` means the underlying map of the product
comparison of `𝒪.module ξ` is injective for every object over `Spec(A)` and
every countable family of modules. -/
theorem ObstructionTheory.natPiComparison_injective_iff {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} (𝒪 : ObstructionTheory X) :
    𝒪.natPiComparison_injective ↔
      ∀ (ξ : ObjectOverSpec X) (M : ℕ → ModuleCat.{u} ξ.carrier),
        Function.Injective (piComparison (𝒪.module ξ) M).hom :=
  sorry

/-- The underlying map of the product comparison of `O_x` is injective. -/
theorem ObstructionTheory.injective_natPiComparison {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} {𝒪 : ObstructionTheory X}
    (h : 𝒪.natPiComparison_injective) (ξ : ObjectOverSpec X)
    (M : ℕ → ModuleCat.{u} ξ.carrier) :
    Function.Injective (piComparison (𝒪.module ξ) M).hom :=
  sorry
end AlgebraicGeometry.GroupoidsOver
