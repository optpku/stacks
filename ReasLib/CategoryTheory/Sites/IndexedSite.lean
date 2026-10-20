/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]

namespace PreZeroHypercover

/-- A selected collection of indexed families is a site when it contains isomorphisms,
is closed under indexed refinement, and admits covering pullback families. -/
class IsSite (coverings : ∀ target : C, Set (PreZeroHypercover.{w} target)) : Prop where
  has_isos : ∀ {S T : C} (f : S ⟶ T) [IsIso f],
    ∃ (indexType : Type w) (_ : Unique indexType),
      ({ I₀ := indexType, X := fun _ => S, f := fun _ => f } : PreZeroHypercover T) ∈
        coverings T
  locality : ∀ {target : C} (family : PreZeroHypercover.{w} target),
    family ∈ coverings target →
      ∀ (refinements : ∀ index, PreZeroHypercover.{w} (family.X index)),
        (∀ index, refinements index ∈ coverings (family.X index)) →
          family.bind refinements ∈ coverings target
  base_change : ∀ {target target' : C} (family : PreZeroHypercover.{w} target),
    family ∈ coverings target → (base : target' ⟶ target) →
      ∃ (pullbackObj : family.I₀ → C)
        (first : ∀ index, pullbackObj index ⟶ target')
        (second : ∀ index, pullbackObj index ⟶ family.X index),
        (∀ index, IsPullback (first index) (second index) base (family.f index)) ∧
          ({ I₀ := family.I₀, X := pullbackObj, f := first } :
            PreZeroHypercover target') ∈ coverings target'

/-- The three axioms defining a selected indexed-family site are equivalent to `IsSite`. -/
theorem IsSite.iff {coverings : ∀ target : C, Set (PreZeroHypercover.{w} target)} :
    IsSite coverings ↔
      (∀ {S T : C} (f : S ⟶ T) [IsIso f],
        ∃ (indexType : Type w) (_ : Unique indexType),
          ({ I₀ := indexType, X := fun _ => S, f := fun _ => f } :
            PreZeroHypercover T) ∈ coverings T) ∧
        (∀ {target : C} (family : PreZeroHypercover.{w} target),
          family ∈ coverings target →
            ∀ (refinements : ∀ index, PreZeroHypercover.{w} (family.X index)),
              (∀ index, refinements index ∈ coverings (family.X index)) →
                family.bind refinements ∈ coverings target) ∧
        (∀ {target target' : C} (family : PreZeroHypercover.{w} target),
          family ∈ coverings target → (base : target' ⟶ target) →
            ∃ (pullbackObj : family.I₀ → C)
              (first : ∀ index, pullbackObj index ⟶ target')
              (second : ∀ index, pullbackObj index ⟶ family.X index),
              (∀ index, IsPullback (first index) (second index) base (family.f index)) ∧
                ({ I₀ := family.I₀, X := pullbackObj, f := first } :
                  PreZeroHypercover target') ∈ coverings target') := sorry

/-- A precoverage induces a selected indexed-family site under its standard stability axioms. -/
instance IsSite.ofPrecoverage (J : Precoverage C) [J.HasIsos] [J.HasPullbacks]
    [J.IsStableUnderBaseChange] [J.IsStableUnderComposition] :
    IsSite (fun target => { family : PreZeroHypercover.{w} target | family.presieve₀ ∈ J target }) :=
  sorry

end PreZeroHypercover

end CategoryTheory
