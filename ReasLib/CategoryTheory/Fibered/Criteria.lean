/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!
# Criteria for fibred functors

This module exposes reusable characterizations of mathlib's canonical `Functor.IsFibered`
predicate without introducing a parallel owner.
-/

@[expose] public section


universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {𝒞 : Type u₁} {𝒮 : Type u₂} [Category.{v₁} 𝒞] [Category.{v₂} 𝒮]

/-- Every morphism of a category is strongly cartesian for its identity functor. -/
theorem IsStronglyCartesian.id {R T : 𝒞} (f : R ⟶ T) :
    IsStronglyCartesian (𝟭 𝒞) f f := sorry
/- Proof strategy: use the canonical identity-functor hom-lift witness. A competing lift over
`g ≫ f` is that composite itself, and its unique factor through `f` is `g`. -/

/-- The identity functor of a category is canonically fibred. -/
instance IsFibered.id : IsFibered (𝟭 𝒞) := sorry
/- Proof strategy: lift `f : R ⟶ T` by `f` itself and apply `IsStronglyCartesian.id f`. -/

/- The reusable mathlib owner is `Functor.IsFibered`;
`CategoryTheory.IsPreFibered.exists_isCartesian` and
`Functor.IsFibered.isStronglyCartesian_of_isCartesian` give the forward source criterion, while
`Functor.IsFibered.of_exists_isStronglyCartesian` gives the converse. The theorem below exposes
that criterion without a parallel fibredness predicate. Writing `f : V ⟶ p.obj x` makes the
source object `U` definitionally `p.obj x`; an arbitrary equality `p.obj x = U` is recovered by
the endpoint transport built into `Functor.IsHomLift`. This form supports downstream conversion in
both directions. -/

/-- A functor `p : 𝒮 ⥤ 𝒞` is fibred exactly when every morphism
`f : V ⟶ p.obj x` admits a strongly cartesian lift `φ : fx ⟶ x` lying over `f`. -/
@[stacks 02XM "fibred categories via strongly cartesian lifts"]
theorem IsFibered.iff_exists_isStronglyCartesian (p : 𝒮 ⥤ 𝒞) :
    p.IsFibered ↔
      ∀ (x : 𝒮) (V : 𝒞) (f : V ⟶ p.obj x),
        ∃ (fx : 𝒮) (φ : fx ⟶ x), p.IsStronglyCartesian f φ := sorry
/- Proof strategy: forward, obtain a cartesian lift from
`IsPreFibered.exists_isCartesian p rfl f` and upgrade it with
`IsFibered.isStronglyCartesian_of_isCartesian`; backward, apply
`IsFibered.of_exists_isStronglyCartesian` directly to the stated family of lifts. -/

end Functor
end CategoryTheory
