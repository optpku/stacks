/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite Unions of Nowhere Dense Sets

This leaf supplies the Boolean-finite closure API missing from Mathlib's
canonical predicate `IsNowhereDense`.
-/

@[expose] public section

universe u

open Set

variable {X : Type u} [TopologicalSpace X]

namespace IsNowhereDense

/-- The union of two nowhere dense subsets is nowhere dense. -/
theorem union {s t : Set X} (hs : IsNowhereDense s) (ht : IsNowhereDense t) :
    IsNowhereDense (s ∪ t) := sorry

/-- Lemma 5.21.2: a finite union of nowhere dense subsets is nowhere dense. -/
@[stacks 03HO]
theorem sUnion {S : Set (Set X)} (hS : S.Finite)
    (h : ∀ s ∈ S, IsNowhereDense s) :
    IsNowhereDense (⋃₀ S) := sorry

end IsNowhereDense
