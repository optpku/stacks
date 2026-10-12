/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.Branches.MinimalPrime
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.109.2 (0C29)

@stack 0C29
-/

open IsLocalRing

universe u v

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

/- Lemma 15.109.2, Stacks `0C29`: equality of branch counts is detected by the radicals of
extended minimal primes of a henselization. -/
@[stacks 0C29 "Lemma 15.109.2, branch equality criterion for completion"]
#check fun
    (iota : IsHenselizationOf.Completion.Comparison (R := A) (Rh := Ah)) ↦
  (IsHenselizationOf.Completion.Comparison.branchNumber_eq_minimalPrimes_iff_radical_map_isPrime
      iota :
    branchNumber A Ah =
        (minimalPrimes (AdicCompletion (maximalIdeal A) A)).encard ↔
      ∀ q : minimalPrimes Ah,
        (Ideal.radical (Ideal.map iota.toAlgHom.toRingHom q)).IsPrime)
