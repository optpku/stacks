/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.Sober
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally Closed Subspaces of Sober Spaces

This module provides the quasi-sobriety and sobriety components of a locally
closed subspace.
-/

@[expose] public section

universe u

open Set Topology

variable {X : Type u} [TopologicalSpace X] {Y : Set X}

/-- Lemma 5.8.7 (2): a locally closed subspace of a quasi-sober space is quasi-sober. -/
@[stacks 0B31 "locally closed subspaces inherit quasi-sobriety"]
protected theorem IsLocallyClosed.quasiSober
    [QuasiSober X] (hY : IsLocallyClosed Y) : QuasiSober Y := sorry

/-- Lemma 5.8.7 (3): a locally closed subspace of a sober space is sober, represented by
Mathlib's `T0Space` and `QuasiSober` components. -/
@[stacks 0B31 "locally closed subspaces inherit sobriety"]
theorem IsLocallyClosed.sober [T0Space X] [QuasiSober X] (hY : IsLocallyClosed Y) :
    T0Space Y ∧ QuasiSober Y := sorry
