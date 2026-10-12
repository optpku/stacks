/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.Projective
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 38.9.1: a finite module over a finite-type algebra is projective over
the Noetherian adically complete base when it is flat, its closed fiber is
projective, and its relative associated primes avoid the extended ideal. -/
@[stacks 05DP] #check
  (Module.Projective.of_adicComplete_of_relativeAssassin :
    ∀ {R : Type u} {S : Type v} {N : Type w},
      [CommRing R] → [CommRing S] → [Algebra R S] →
      [AddCommGroup N] → [Module S N] → [Module R N] → [IsScalarTower R S N] →
      (I : Ideal R) → [IsNoetherianRing R] → [Algebra.FiniteType R S] →
      [IsAdicComplete I R] → [Module.Finite S N] → [Module.Flat R N] →
      [Module.Projective (R ⧸ I) (N ⧸ (I • (⊤ : Submodule R N)))] →
      (∀ q : PrimeSpectrum S, q ∈ relativeAssassin R S N →
        I.map (algebraMap R S) + q.asIdeal ≠ ⊤) →
      Module.Projective R N)
