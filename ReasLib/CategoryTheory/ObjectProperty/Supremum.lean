/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsClosure
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.Order.Directed
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.FiniteCoproductClosure

@[expose] public section

/-!
# Suprema of Object-Property Closures

This leaf records the generic interchange between directed or monotone unions
and colimit, finite-coproduct, or retract closure.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory.ObjectProperty

section

variable {C : Type u} [Category.{v} C]

/-- A supremum of a directed nonempty family of object properties closed under finite colimits is
closed under those colimits. -/
@[stacks 0FX6]
theorem iSup_isClosedUnderColimitsOfShape_of_directed
    {ι : Type*} [Nonempty ι] {J : Type*} [Category J] [Finite J]
    (P : ι → ObjectProperty C) (hP : Directed (· ≤ ·) P)
    [∀ i, (P i).IsClosedUnderIsomorphisms] [∀ i, (P i).IsClosedUnderColimitsOfShape J] :
    (⨆ i, P i).IsClosedUnderColimitsOfShape J := sorry

/-- Colimit closure commutes with the supremum of a directed nonempty family when all generating
colimit shapes are finite. -/
@[stacks 0FX6]
theorem colimitsClosure_iSup_of_directed {ι : Type*} [Nonempty ι] {α : Type*} (J : α → Type*)
    [∀ a, Category (J a)] [∀ a, Finite (J a)]
    (P : ι → ObjectProperty C) (hP : Directed (· ≤ ·) P) :
    (⨆ i, P i).colimitsClosure J = ⨆ i, (P i).colimitsClosure J := sorry

/-- Additive closure commutes with the supremum of a directed nonempty family. -/
@[stacks 0FX6]
theorem additiveClosure_iSup_of_directed {ι : Type*} [Nonempty ι]
    (P : ι → ObjectProperty C) (hP : Directed (· ≤ ·) P) :
    additiveClosure (⨆ i, P i) = ⨆ i, additiveClosure (P i) := sorry

/-- A supremum of a monotone sequence of object properties closed under finite colimits is
closed under those colimits. -/
@[stacks 0FX6]
theorem iSup_isClosedUnderColimitsOfShape_of_monotone
    {J : Type*} [Category J] [Finite J] (P : ℕ → ObjectProperty C) (hP : Monotone P)
    [∀ n, (P n).IsClosedUnderIsomorphisms] [∀ n, (P n).IsClosedUnderColimitsOfShape J] :
    (⨆ n, P n).IsClosedUnderColimitsOfShape J := sorry

/-- Colimit closure commutes with the supremum of a monotone sequence when all generating
colimit shapes are finite. -/
@[stacks 0FX6]
theorem colimitsClosure_iSup_of_monotone {α : Type*} (J : α → Type*)
    [∀ a, Category (J a)] [∀ a, Finite (J a)]
    (P : ℕ → ObjectProperty C) (hP : Monotone P) :
    (⨆ n, P n).colimitsClosure J = ⨆ n, (P n).colimitsClosure J := sorry

/-- Additive closure commutes with the supremum of a monotone sequence. -/
@[stacks 0FX6]
theorem additiveClosure_iSup_of_monotone (P : ℕ → ObjectProperty C) (hP : Monotone P) :
    additiveClosure (⨆ n, P n) = ⨆ n, additiveClosure (P n) := sorry

/-- Retract closure commutes with an arbitrary supremum. -/
@[stacks 0FX6]
theorem retractClosure_iSup {ι : Sort*} (P : ι → ObjectProperty C) :
    (⨆ i, P i).retractClosure = ⨆ i, (P i).retractClosure := sorry

end

end CategoryTheory.ObjectProperty
