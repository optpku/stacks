/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sets of representatives for essentially small object properties

This file turns Mathlib's categorical `ObjectProperty.EssentiallySmall` API into the equivalent
existence of a set containing exactly one representative of every isomorphism class satisfying
the property.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- An essentially small,
isomorphism-closed property admits a set containing exactly one representative of each
isomorphism class. -/
@[stacks 040B "object-property form"]
theorem EssentiallySmall.exists_set_representatives
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    [ObjectProperty.EssentiallySmall.{w} P] :
    ∃ S : Set C,
      (∀ X ∈ S, P X) ∧
      ∀ X : C, P X → ∃! Y : C, Y ∈ S ∧ Nonempty (Y ≅ X) := sorry

/-- A property that is essentially small relative to the universe `w` admits a family of
objects satisfying it, indexed by a type in `Type w`, such that every object satisfying the
property is isomorphic to a member of the family. -/
theorem EssentiallySmall.exists_family_representatives
    (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{w} P] :
    ∃ (T : Type w) (F : T → C), (∀ t, P (F t)) ∧
      ∀ X : C, P X → ∃ t, Nonempty (F t ≅ X) := by
  obtain ⟨Q, _, hQP, hPQ⟩ := EssentiallySmall.exists_small_le.{w} P
  refine ⟨Shrink.{w} (Subtype Q), fun t ↦ ((equivShrink _).symm t).1,
    fun t ↦ hQP _ ((equivShrink _).symm t).2, fun X hX ↦ ?_⟩
  obtain ⟨Y, hY, ⟨e⟩⟩ := hPQ X hX
  refine ⟨equivShrink _ ⟨Y, hY⟩, ⟨?_⟩⟩
  change ((equivShrink (Subtype Q)).symm (equivShrink (Subtype Q) ⟨Y, hY⟩)).1 ≅ X
  rw [Equiv.symm_apply_apply]
  exact e.symm

end CategoryTheory.ObjectProperty
