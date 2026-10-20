/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.LocalizationAtPrime
import StacksCheckRecall

/-!
# Lemma 15.67.15

@stack 0B67

For a map `A → B` and `K ∈ D(B)`, Tor-amplitude of `K` over `A` is equivalent to the
corresponding condition after localization at every prime of `B`; it is enough to test maximal
ideals.  ReasLib states the result for an explicit ring homomorphism and uses the canonical local
ring maps at target primes.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 15.67.15 recalls the explicit-map owner below. -/
@[stacks 0B67 "Lemma 15.67.15"]
#check fun {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (K : DerivedCategory (ModuleCat B)) (a b : ℤ) ↦
  (DerivedCategory.HasTorAmplitudeIn.localizationAtPrime_tfae
      (f := f) (K := K) (a := a) (b := b) :
    List.TFAE [
      DerivedCategory.HasTorAmplitudeIn (R := A)
        ((ModuleCat.derivedRestrictionOfScalars f).obj K) a b,
      ∀ q : PrimeSpectrum B,
        DerivedCategory.HasTorAmplitudeIn (R := f.sourceLocalRingAt q)
          (DerivedCategory.localizedAtPrime f K q) a b,
      ∀ m : MaximalSpectrum B,
        DerivedCategory.HasTorAmplitudeIn (R := f.sourceLocalRingAt m.toPrimeSpectrum)
          (DerivedCategory.localizedAtPrime f K m.toPrimeSpectrum) a b])
