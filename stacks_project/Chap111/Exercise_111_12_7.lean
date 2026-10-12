/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Connected
public import ReasLib.RingTheory.Ideal.MinimalPrime.TwoMinimalPrimes
import StacksCheckRecall

@[expose] public section

open scoped ENat

universe u

/- Exercise 111.12.7: interpret the two distinct minimal primes as the complete
pair `minimalPrimes R = {p, q}`; then the quotient sequence is short exact. -/
@[stacks 0CT1] #check
  (Ideal.quotientProdSup_shortExact :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R]
      {p q : Ideal R},
      minimalPrimes R = {p, q} → p ≠ q →
        (Ideal.quotientProdSupShortComplex p q).ShortExact)

#check
  (Ideal.ringKrullDim_quotient_add_ge_one_of_moduleDepth_ge_two :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R]
      {p q : Ideal R},
      minimalPrimes R = {p, q} → p ≠ q → (2 : ℕ∞) ≤ moduleDepth R R →
        1 ≤ ringKrullDim (R ⧸ (p + q)))

#check
  (AlgebraicGeometry.PuncturedSpectrum.connectedSpace_of_moduleDepth_ge_two :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      (2 : ℕ∞) ≤ moduleDepth R R →
        ConnectedSpace (AlgebraicGeometry.PuncturedSpectrum.scheme R))
