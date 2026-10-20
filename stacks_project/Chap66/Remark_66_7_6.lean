/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GermProperty.LocalRing.Examples
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocalRingProperty
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Remark 66.7.6. If `P` is a property of local rings invariant under étale ring maps at corresponding
primes, then `𝒫(U, u) := P(𝒪_{U, u})` is an étale-local property of scheme germs. In
this situation, “the local ring of `X` at `x` has `P`” means `X` has this germ property
at `x`. -/
@[stacks 0BBL] #check
  (AlgebraicGeometry.GermProperty.ofLocalRing.isEtaleLocal :
    ∀ {P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop},
      LocalRingProperty.RespectsIso P → LocalRingProperty.IsEtaleLocalAtPrimes P →
        (AlgebraicGeometry.GermProperty.ofLocalRing P).IsEtaleLocal)
#check (AlgebraicGeometry.AlgebraicSpace.localRingHas :
  ∀ {S : Scheme.{u}} (P : ∀ (R : Type u) [CommRing R] [IsLocalRing R], Prop)
    (X : AlgebraicGeometry.AlgebraicSpace S) (x : AlgebraicGeometry.AlgebraicSpace.Points X),
    Prop)

/- Remark 66.7.6 (1): Noetherianity of local rings is étale-local at corresponding primes. -/
@[stacks 0BBL] #check
  (Algebra.Etale.localizationAtPrime_isNoetherianRing_iff :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
      (q : PrimeSpectrum B),
      IsNoetherianRing (Localization.AtPrime (q.asIdeal.under A)) ↔
        IsNoetherianRing (Localization.AtPrime q.asIdeal))

/- Remark 66.7.6 (2): having Krull dimension `d` is étale-local at corresponding primes. -/
@[stacks 0BBL] #check
  (Algebra.Etale.ringKrullDim_localizationAtPrime_eq :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
      (q : Ideal B) [q.IsPrime],
      ringKrullDim (Localization.AtPrime (q.under A)) =
        ringKrullDim (Localization.AtPrime q))

/- Remark 66.7.6 (3): regularity of local rings is étale-local at corresponding primes. -/
@[stacks 0BBL] #check
  (Algebra.Etale.localizationAtPrime_isRegularLocalRing_iff :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
      (q : PrimeSpectrum B),
      IsRegularLocalRing (Localization.AtPrime (q.asIdeal.under A)) ↔
        IsRegularLocalRing (Localization.AtPrime q.asIdeal))

/- Remark 66.7.6 (4): being a discrete valuation ring is étale-local at corresponding
primes. -/
@[stacks 0BBL] #check
  (LocalRingProperty.isDiscreteValuationRing_isEtaleLocalAtPrimes :
    LocalRingProperty.IsEtaleLocalAtPrimes LocalRingProperty.isDiscreteValuationLocalRing)

/- Remark 66.7.6 (5): reducedness of local rings is étale-local at corresponding primes. -/
@[stacks 0BBL] #check
  (LocalRingProperty.isReduced_isEtaleLocalAtPrimes :
    LocalRingProperty.IsEtaleLocalAtPrimes fun R ↦ _root_.IsReduced R)

/- Remark 66.7.6 (6): normality of local rings is étale-local at corresponding primes. -/
@[stacks 0BBL] #check
  (LocalRingProperty.isNormalRing_isEtaleLocalAtPrimes :
    LocalRingProperty.IsEtaleLocalAtPrimes fun R ↦ IsNormalRing R)

/- Remark 66.7.6 (7): being Noetherian of depth `k` is étale-local at corresponding primes. -/
@[stacks 0BBL] #check
  (LocalRingProperty.isNoetherianOfDepth_isEtaleLocalAtPrimes :
    ∀ k : ℕ, LocalRingProperty.IsEtaleLocalAtPrimes (LocalRingProperty.isNoetherianOfDepth k))

/- Remark 66.7.6 (8): being Noetherian and Cohen–Macaulay is étale-local at corresponding
primes. -/
@[stacks 0BBL] #check
  (LocalRingProperty.isNoetherianCohenMacaulay_isEtaleLocalAtPrimes :
    LocalRingProperty.IsEtaleLocalAtPrimes LocalRingProperty.isNoetherianCohenMacaulay)

/- Remark 66.7.6 (9): being Noetherian and Gorenstein is étale-local at corresponding
primes. -/
@[stacks 0BBL] #check
  (LocalRingProperty.isGorensteinLocalRing_isEtaleLocalAtPrimes :
    LocalRingProperty.IsEtaleLocalAtPrimes fun R ↦ IsGorensteinLocalRing R)
