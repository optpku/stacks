/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cardinality of roots of unity

For nonzero `n`, the finite cyclic group of `n`th roots of unity in a domain has order dividing
`n`. This is kept separate from the power-map construction so both APIs can be imported
independently.

@stack 09EE
-/

universe u

namespace rootsOfUnity

/-- The cardinality of the `n`th roots of unity in an integral domain divides nonzero `n`. -/
@[stacks 09EE "cardinality of roots of unity divides the index"]
theorem natCard_dvd {R : Type u} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n] :
    Nat.card (rootsOfUnity n R) ∣ n := sorry

end rootsOfUnity
