/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Constructible
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Retrocompact Constructible Sets

Constructible subsets are retrocompact without any ambient separation or
spectrality assumption.
-/

@[expose] public section

universe u

open Set TopologicalSpace

namespace Topology

variable {X : Type u} [TopologicalSpace X] {E : Set X}

/-- Lemma 5.15.10: every constructible subset is retrocompact. -/
@[stacks 09YH]
theorem IsConstructible.isRetrocompact (hE : IsConstructible E) : IsRetrocompact E := sorry

/-- A constructible subset of a compact space, bundled as a compact subset. -/
@[stacks 09YH "constructible subset as a compact subset"]
def IsConstructible.toCompacts [CompactSpace X]
    (hE : IsConstructible E) : Compacts X :=
  ⟨E, hE.isRetrocompact.isCompact⟩

/-- The compact subset associated to a constructible subset has the original carrier. -/
@[simp]
theorem IsConstructible.coe_toCompacts [CompactSpace X]
    (hE : IsConstructible E) : (hE.toCompacts : Set X) = E := sorry

end Topology
