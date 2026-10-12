/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Separation Alternatives in Spectral Spaces

This module records the spectral-space dichotomy between a common
specialization and separation by open neighborhoods.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

namespace SpectralSpace

/-- Lemma 5.23.7: two points of a spectral space have a common specialization
or have disjoint open neighborhoods. -/
@[stacks 0904]
theorem exists_commonSpecialization_or_separatedNhds (x y : X) :
    (∃ z : X, z ⤳ x ∧ z ⤳ y) ∨ SeparatedNhds ({x} : Set X) ({y} : Set X) := sorry

end SpectralSpace
