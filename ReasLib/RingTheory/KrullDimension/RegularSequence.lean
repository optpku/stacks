/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Sequence.Regularity.Append

/-!
# Krull dimension and regular-sequence prefixes

This leaf records the dimension formula for a prefix of a regular sequence.
It is independent of Cohen--Macaulayness and therefore belongs with Krull
dimension rather than the Cohen--Macaulay package.

@stack 02JN
-/

@[expose] public section

universe u

namespace RingTheory.Sequence.IsRegular

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The quotient by any prefix of a regular sequence has the expected Krull
dimension drop. -/
@[stacks 02JN "regular-sequence prefix dimension"]
theorem ringKrullDim_quotient_take_add_eq
    {xs : List R} (hreg : IsRegular R xs) {i : ℕ} (hi : i ≤ xs.length) :
    ringKrullDim (R ⧸ Ideal.ofList (xs.take i)) + i = ringKrullDim R := sorry

end RingTheory.Sequence.IsRegular
