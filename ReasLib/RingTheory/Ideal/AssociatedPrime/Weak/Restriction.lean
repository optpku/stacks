/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Restriction
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.FiniteGeneration
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weakly associated primes under restriction of scalars

This module relates weakly associated primes before and after restriction of scalars. When the
larger scalar ring is Noetherian, it also identifies the weak and exact associated-prime sets
that occur in the restriction chain.
-/

@[expose] public section

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

namespace weaklyAssociatedPrimes.Restriction

/-- Weakly associated primes after restricting scalars are contained in the contraction image
of the weakly associated primes over the larger ring. -/
@[stacks 05C6 "weak restriction inclusion"]
theorem subset_comap_image :
    weaklyAssociatedPrimes R M ⊆
      Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M := sorry

/-- When the larger scalar ring is Noetherian, the weakly associated primes after restriction
are exactly the contraction image of the weakly associated primes over the larger ring. -/
@[stacks 05C7 "Noetherian weak restriction equality"]
theorem eq_image_comap_of_isNoetherianRing
    [IsNoetherianRing S] :
    weaklyAssociatedPrimes R M =
      Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M := sorry

/-- Weakly associated primes commute with restriction of scalars along a finite ring map. -/
@[stacks 05E1]
theorem eq_image_comap_of_finite [Module.Finite R S] :
    weaklyAssociatedPrimes R M =
      Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M := sorry

end weaklyAssociatedPrimes.Restriction

namespace associatedPrimesOfModule.Restriction

/-- If the larger scalar ring is Noetherian, exact associated primes after restriction coincide
with weakly associated primes over the base ring. -/
@[stacks 05C7 "Noetherian exact/weak equality after restriction"]
theorem eq_weaklyAssociatedPrimes_of_isNoetherianRing
    [IsNoetherianRing S] :
    associatedPrimesOfModule R M = weaklyAssociatedPrimes R M := sorry

end associatedPrimesOfModule.Restriction

namespace associatedPrimesOfModule.Restriction

/-- The contraction image of the exact associated primes, the exact and weak associated primes
after restriction, and the contraction image of the weakly associated primes form an inclusion
chain. -/
@[stacks 05C7 "source restriction chain"]
theorem weaklyAssociatedPrimes_chain :
    List.IsChain (· ⊆ ·)
      [Ideal.comap (algebraMap R S) '' associatedPrimesOfModule S M,
        associatedPrimesOfModule R M,
        weaklyAssociatedPrimes R M,
        Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M] := sorry

/-- When `S` is Noetherian, all four sets in the restriction-of-scalars associated-prime chain
are equal. -/
@[stacks 05C7 "Noetherian source restriction equality chain"]
theorem weaklyAssociatedPrimes_eq_chain_of_isNoetherianRing
    [IsNoetherianRing S] :
    List.IsChain (· = ·)
      [Ideal.comap (algebraMap R S) '' associatedPrimesOfModule S M,
        associatedPrimesOfModule R M,
        weaklyAssociatedPrimes R M,
        Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M] := sorry

end associatedPrimesOfModule.Restriction

end
