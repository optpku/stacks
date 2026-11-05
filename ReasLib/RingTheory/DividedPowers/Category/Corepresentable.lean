/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Corepresentable
public import ReasLib.RingTheory.DividedPowers.Category.Limits

@[expose] public section

/-!
# Corepresentability of Functors on Divided Power Rings

This leaf turns a uniform cardinal bound on sources of elements into the small generating family
used by the standard corepresentability criterion.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Functor

variable (F : DividedPowerRing.{u} ⥤ Type u)

/-- The elements of `F` have sources bounded by `κ` when every element is the image of an element
over a divided power ring of cardinality at most `κ`. -/
@[stacks 07GW "bounded sources of functor elements"]
def ElementsBoundedBy (κ : Cardinal.{u}) : Prop :=
  ∀ ⦃A : DividedPowerRing.{u}⦄ (x : F.obj A),
    ∃ (A' : DividedPowerRing.{u}) (φ : A' ⟶ A) (x' : F.obj A'),
      F.map φ x' = x ∧ Cardinal.mk A' ≤ κ

/-- A cardinal bound on sources remains valid after enlarging the bound. -/
theorem ElementsBoundedBy.mono {κ κ' : Cardinal.{u}}
    (h : F.ElementsBoundedBy κ) (hκ : κ ≤ κ') :
    F.ElementsBoundedBy κ' := sorry

/-- A bounded-source condition supplies a small family which generates every functor element by
functorial images. The index type lies in the universe of morphisms, so the family can be
used by `isCorepresentable_of_preservesLimits_of_generating_family` without any further
smallness hypothesis. No limit-preservation assumption is needed for this step. -/
theorem ElementsBoundedBy.exists_generating_family {κ : Cardinal.{u}}
    (h : F.ElementsBoundedBy κ) :
    ∃ (ι : Type u) (X : ι → DividedPowerRing.{u}) (x : ∀ i, F.obj (X i)),
      ∀ ⦃A : DividedPowerRing.{u}⦄ (y : F.obj A),
        ∃ (i : ι) (φ : X i ⟶ A), F.map φ (x i) = y := sorry

/-- A functor has bounded element sources when one cardinal bounds sources for all its elements. -/
def HasBoundedElementSources : Prop :=
  ∃ κ : Cardinal.{u}, F.ElementsBoundedBy κ

namespace HasBoundedElementSources

variable [PreservesLimits F]

/-- Lemma 23.3.3 (Tag 07GW): a limit-preserving functor from divided power rings to types is
corepresentable when its elements have uniformly bounded sources. -/
@[stacks 07GW]
theorem isCorepresentable (h : F.HasBoundedElementSources) :
    F.IsCorepresentable := by
  obtain ⟨κ, hκ⟩ := h
  obtain ⟨ι, X, x, h_generate⟩ := hκ.exists_generating_family F
  exact F.isCorepresentable_of_preservesLimits_of_generating_family X x h_generate

end HasBoundedElementSources

end CategoryTheory.Functor
