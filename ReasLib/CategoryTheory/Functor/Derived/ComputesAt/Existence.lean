module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Existence from Computing Objects

This leaf turns objectwise computing data along denominators into source-defined derived functors
everywhere. The primary conclusions retain essential constancy; weaker Mathlib pointwise
Kan-extension existence is exposed as a companion API. The construction is independent of any
concrete derived-category model.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']

/-- Stacks 05T1 (1): if every object maps through a denominator to one which computes the
right-derived value, then that right-derived functor is source-defined everywhere. -/
@[stacks 05T1]
theorem RightDerived.EverywhereDefined.of_exists_computesAt
    (F : D ⥤ D') (S : MorphismProperty D) [S.ContainsIdentities]
    (h : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), S s ∧ RightDerived.ComputesAt F S X') :
    Functor.RightDerived.EverywhereDefined F S := sorry

/-- Stacks 05T1: if every object maps through a denominator to one which computes the pointwise
right-derived value of `F`, then `F` has a pointwise right-derived functor everywhere. -/
@[stacks 05T1]
theorem RightDerived.EverywhereDefined.hasPointwise_of_exists_computesAt
    (F : D ⥤ D') (S : MorphismProperty D) [S.ContainsIdentities]
    (h : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), S s ∧ RightDerived.ComputesAt F S X') :
    F.HasPointwiseRightDerivedFunctor S := sorry

/-- Stacks 05T1 (2): if every object receives a denominator from one which computes the
left-derived value, then that left-derived functor is source-defined everywhere. -/
@[stacks 05T1]
theorem LeftDerived.EverywhereDefined.of_exists_computesAt
    (F : D ⥤ D') (S : MorphismProperty D) [S.ContainsIdentities]
    (h : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), S s ∧ LeftDerived.ComputesAt F S X') :
    Functor.LeftDerived.EverywhereDefined F S := sorry

/-- Stacks 05T1: if every object receives a denominator from one which computes the pointwise
left-derived value of `F`, then `F` has a pointwise left-derived functor everywhere. -/
@[stacks 05T1]
theorem LeftDerived.EverywhereDefined.hasPointwise_of_exists_computesAt
    (F : D ⥤ D') (S : MorphismProperty D) [S.ContainsIdentities]
    (h : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), S s ∧ LeftDerived.ComputesAt F S X') :
    F.HasPointwiseLeftDerivedFunctor S := sorry


end CategoryTheory.Functor
