/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite Krull Dimension

This leaf provides the order-theoretic bridge from a finite upper bound on
`ringKrullDim R` to a natural-valued dimension.
-/

universe u

namespace FiniteRingKrullDim

/-- A ring with finite Krull dimension has a natural-number-valued Krull dimension. -/
@[stacks 00KQ "natural-valued finite Krull dimension"]
theorem exists_eq_nat
    {R : Type u} [CommRing R] [FiniteRingKrullDim R] :
    ∃ n : ℕ, ringKrullDim R = n := sorry

end FiniteRingKrullDim

/-- A nontrivial ring whose Krull dimension is bounded by a natural number has
a natural-valued Krull dimension no larger than that bound. -/
@[stacks 00KQ "natural-valued finite Krull dimension"]
theorem ringKrullDim_eq_nat_of_le
    {R : Type u} [CommRing R] [Nontrivial R] {d : ℕ}
    (h : ringKrullDim R ≤ d) :
    ∃ n : ℕ, n ≤ d ∧ ringKrullDim R = n := sorry
