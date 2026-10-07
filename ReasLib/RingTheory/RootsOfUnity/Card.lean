module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cardinality of roots of unity

The finite cyclic group of `n`th roots of unity in a domain has order dividing `n`.  This is kept
separate from the power-map construction so both APIs can be imported independently.

@stack 09EE
-/

universe u

namespace rootsOfUnity

variable {R : Type u} [CommMonoid R] {n : ℕ} [NeZero n]

/-- The cardinality of the `n`th roots of unity divides `n` in a commutative monoid. -/
@[stacks 09EE "cardinality of roots of unity divides the index"]
theorem natCard_dvd : Nat.card (rootsOfUnity n R) ∣ n := sorry

end rootsOfUnity
