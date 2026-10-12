/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Principality
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 31.15.10: Let `R` be a Noetherian unique factorization domain and let `I ⊆ R` be an
ideal. If `R ⧸ I` has no embedded primes and every minimal prime over `I` has height one, then
`I` is principal. -/
@[stacks 0BXI] #check
  (Ideal.isPrincipal_of_noEmbedded_of_minimalPrimes_height_eq_one :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
      [IsNoetherianRing R] (I : Ideal R), embeddedPrimes (R ⧸ I) = ∅ →
        (∀ p ∈ I.minimalPrimes, p.height = 1) → I.IsPrincipal)
