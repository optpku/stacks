/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Dualizable objects in monoidal categories

@stack 0FFR

This leaf packages existence of a left or right dual as an object property.  Chosen duality data
remain owned by Mathlib's `HasLeftDual`, `HasRightDual`, and `ExactPairing`; the predicates here
only provide a stable proposition-valued surface for geometric finiteness theorems.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Objects admitting a chosen left dual, as an object property. -/
@[stacks 0FFR "left-dualizable object property"]
def leftDualizable : ObjectProperty C :=
  fun X => Nonempty (HasLeftDual X)

/-- An object is left dualizable when some object forms an exact pairing with it. -/
abbrev IsLeftDualizable (X : C) : Prop :=
  leftDualizable X

/-- Objects admitting a chosen right dual, as an object property. -/
@[stacks 0FFR "right-dualizable object property"]
def rightDualizable : ObjectProperty C :=
  fun X => Nonempty (HasRightDual X)

/-- An object is right dualizable when it forms an exact pairing with some object. -/
abbrev IsRightDualizable (X : C) : Prop :=
  rightDualizable X

namespace ExactPairing

/-- Explicit exact-pairing data exhibit the second object as left dualizable. -/
@[implicit_reducible]
def toHasLeftDual {X Y : C} (p : ExactPairing X Y) : HasLeftDual Y where
  leftDual := X
  exact := p

/-- Explicit exact-pairing data exhibit the first object as right dualizable. -/
@[implicit_reducible]
def toHasRightDual {X Y : C} (p : ExactPairing X Y) : HasRightDual X where
  rightDual := Y
  exact := p

/-- Swap explicit exact-pairing data in a braided monoidal category.  Unlike Mathlib's
`BraidedCategory.exactPairing_swap`, this bridge takes the pairing as ordinary data rather than
requiring callers to install it as a temporary instance. -/
@[stacks 0FFR "braided exact-pairing swap", implicit_reducible]
def braidedSwap [BraidedCategory C] {X Y : C} (p : ExactPairing X Y) :
    ExactPairing Y X :=
  @BraidedCategory.exactPairing_swap C _ _ _ X Y p

end ExactPairing

/-- An explicit left-dual pairing implies left dualizability. -/
theorem IsLeftDualizable.of_exactPairing
    {X Y : C} (p : ExactPairing X Y) :
    IsLeftDualizable Y :=
  ⟨p.toHasLeftDual⟩

/-- An explicit right-dual pairing implies right dualizability. -/
theorem IsRightDualizable.of_exactPairing
    {X Y : C} (p : ExactPairing X Y) :
    IsRightDualizable X :=
  ⟨p.toHasRightDual⟩

/-- Left dualizability is equivalent to the existence of explicit exact-pairing data. -/
theorem isLeftDualizable_iff_exists_exactPairing (Y : C) :
    IsLeftDualizable Y ↔ ∃ X : C, Nonempty (ExactPairing X Y) := by
  constructor
  · rintro ⟨hY⟩
    exact ⟨hY.leftDual, ⟨hY.exact⟩⟩
  · rintro ⟨X, ⟨p⟩⟩
    exact .of_exactPairing p

/-- Right dualizability is equivalent to the existence of explicit exact-pairing data. -/
theorem isRightDualizable_iff_exists_exactPairing (X : C) :
    IsRightDualizable X ↔ ∃ Y : C, Nonempty (ExactPairing X Y) := by
  constructor
  · rintro ⟨hX⟩
    exact ⟨hX.rightDual, ⟨hX.exact⟩⟩
  · rintro ⟨Y, ⟨p⟩⟩
    exact .of_exactPairing p

section Braided

variable [BraidedCategory C]

/-- In a braided monoidal category, left and right dualizability are equivalent. -/
theorem isLeftDualizable_iff_isRightDualizable (X : C) :
    IsLeftDualizable X ↔ IsRightDualizable X := by
  rw [isLeftDualizable_iff_exists_exactPairing,
    isRightDualizable_iff_exists_exactPairing]
  constructor
  · rintro ⟨Y, ⟨p⟩⟩
    exact ⟨Y, ⟨p.braidedSwap⟩⟩
  · rintro ⟨Y, ⟨p⟩⟩
    exact ⟨Y, ⟨p.braidedSwap⟩⟩

/-- In a braided monoidal category, a right-dualizable object is left-dualizable. -/
@[stacks 0FFR "right to left"]
theorem IsRightDualizable.isLeftDualizable
    {X : C} (hX : IsRightDualizable X) :
    IsLeftDualizable X :=
  (isLeftDualizable_iff_isRightDualizable X).2 hX

/-- In a braided monoidal category, a left-dualizable object is right-dualizable. -/
@[stacks 0FFR "left to right"]
theorem IsLeftDualizable.isRightDualizable
    {X : C} (hX : IsLeftDualizable X) :
    IsRightDualizable X :=
  (isLeftDualizable_iff_isRightDualizable X).1 hX

end Braided

end CategoryTheory


