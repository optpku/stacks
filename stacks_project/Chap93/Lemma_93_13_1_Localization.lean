/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Basic
public import stacks_project.Chap93.Lemma_93_12_3_Lift

/-!
# Flat algebra lifts versus localization

This leaf owns the syntomic-at-primes-meeting-a-submonoid hypothesis and the
comparison of flat lifts of `B` with flat lifts of `Localization S`.
-/

@[expose] public section

universe u v

namespace RingHom

/-- A ring homomorphism is syntomic at every prime of the target that meets a
given submonoid. -/
def SyntomicAtPrimesMeeting {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Submonoid S) : Prop :=
  ∀ q : PrimeSpectrum S, ¬ M ≤ q.asIdeal.primeCompl → f.SyntomicAtPrime q

namespace SyntomicAtPrimesMeeting

/-- Syntomicity at primes meeting `M` is equivalent to: every non-syntomic prime
of the target is disjoint from `M`. -/
theorem iff {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Submonoid S) :
    f.SyntomicAtPrimesMeeting M ↔
      ∀ q : PrimeSpectrum S, ¬ f.SyntomicAtPrime q → M ≤ q.asIdeal.primeCompl :=
  sorry

end SyntomicAtPrimesMeeting

end RingHom

namespace Algebra.NilpotentLift

/-- For a surjection of Noetherian rings with nilpotent kernel, a finite-type
flat algebra, and a submonoid meeting only syntomic primes, a flat lift exists
if and only if the localization at that submonoid admits a flat lift. -/
theorem existsFlatLift_iff_existsFlatLift_localization
    {A' A B : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B] [IsNoetherianRing A'] [IsNoetherianRing A]
    [Algebra.FiniteType A B] [Module.Flat A B]
    (hsurj : Function.Surjective (algebraMap A' A))
    (hker : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (S : Submonoid B) (hsyn : (algebraMap A B).SyntomicAtPrimesMeeting S) :
    existsFlatLift A' A B ↔ existsFlatLift A' A (Localization S) :=
  sorry

end Algebra.NilpotentLift

end
