/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sober
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sobriety on Covers

This module complements Mathlib's quasi-sober open-cover API with the matching
Kolmogorov and sober-component interfaces.
-/

@[expose] public section

universe u v

open Set TopologicalSpace

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/-- Lemma 5.8.8 (1): the Kolmogorov property is local on a cover by locally closed subsets. -/
@[stacks 06N9 "Kolmogorov spaces are local on locally closed covers"]
theorem t0Space_iff_forall_of_locallyClosed_cover
    (S : ι → Set X) (hcover : ⋃ i, S i = univ) (hloc : ∀ i, IsLocallyClosed (S i)) :
    T0Space X ↔ ∀ i, T0Space (S i) := sorry

namespace TopologicalSpace.IsOpenCover

/-- Lemma 5.8.8 (3), Kolmogorov component: the Kolmogorov property is local on an open cover. -/
@[stacks 06N9 "Kolmogorov spaces are local on open covers"]
theorem t0Space_iff_forall {U : ι → Opens X} (hU : IsOpenCover U) :
    T0Space X ↔ ∀ i, T0Space (U i) := sorry

/-- Lemma 5.8.8 (3), sober form: sobriety is local on an open cover, expressed through
Mathlib's `T0Space` and `QuasiSober` components. -/
@[stacks 06N9 "sober spaces are local on open covers"]
theorem sober_iff_forall {U : ι → Opens X} (hU : IsOpenCover U) :
    (T0Space X ∧ QuasiSober X) ↔ ∀ i, T0Space (U i) ∧ QuasiSober (U i) := sorry

end TopologicalSpace.IsOpenCover
