module

public import ReasLib.RingTheory.AdicCompletion.Branches
public import ReasLib.RingTheory.Henselian.Henselization.Completion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Branch equality and minimal primes of a completion

The equality between the branch number of a Noetherian local ring and the number of minimal
primes of its completion is detected pointwise on minimal primes of a henselization.

@stack 0C29
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u v

namespace IsHenselizationOf.Completion.Comparison

/-- Lemma 15.109.2, Stacks `0C29`: the branch number of a Noetherian local ring equals the
minimal-prime count of its completion exactly when the radical of every henselization minimal
prime extended along the canonical comparison is prime. -/
@[stacks 0C29 "branch equality criterion via minimal primes of the completion"]
theorem branchNumber_eq_minimalPrimes_iff_radical_map_isPrime
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
    (iota : IsHenselizationOf.Completion.Comparison (R := A) (Rh := Ah)) :
    branchNumber A Ah =
        (minimalPrimes (AdicCompletion (maximalIdeal A) A)).encard ↔
      ∀ q : minimalPrimes Ah,
        (Ideal.radical (Ideal.map iota.toAlgHom.toRingHom q)).IsPrime := sorry
-- Proof strategy: use the surjective minimal-prime comparison from `0C28`; equality of the
-- finite `encard` values is equivalent to singleton fibers, which are detected by primality of
-- the radical of the extended minimal prime.

end IsHenselizationOf.Completion.Comparison
