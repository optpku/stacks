/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import ReasLib.RingTheory.RingHom.Local.AtPrime
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor-amplitude after localization at target primes

@stack 0B67

For an explicit ring homomorphism `f : A →+* B`, Tor-amplitude of a derived `B`-module over
`A` can be detected after localizing at every prime, or only at every maximal ideal, of `B`.
The localized source ring and its map to the localized target are the canonical
`f.sourceLocalRingAt q` and `f.localRingHomAt q`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The derived `B`-module obtained by localizing at a target prime and then restricting along the
induced map from the contracted source local ring. -/
@[stacks 0B67 "derived localization at a target prime"]
noncomputable abbrev localizedAtPrime
    (f : A →+* B) (K : DerivedCategory (ModuleCat B)) (q : PrimeSpectrum B) :
    DerivedCategory (ModuleCat (f.sourceLocalRingAt q)) :=
  (ModuleCat.derivedRestrictionOfScalars (f.localRingHomAt q)).obj
    ((ModuleCat.derivedExtensionOfScalars
      (algebraMap B (Localization.AtPrime q.asIdeal))).obj K)

namespace HasTorAmplitudeIn

/-- Lemma 15.67.15 (Stacks `0B67`): Tor-amplitude after restriction along `f` is equivalent to
the corresponding condition after localization at every prime of `B`, and it is enough to test
the maximal ideals of `B`. -/
@[stacks 0B67 "Tor-amplitude detected at target primes"]
theorem localizationAtPrime_tfae
    (f : A →+* B) (K : DerivedCategory (ModuleCat B)) {a b : ℤ} :
    List.TFAE [
      HasTorAmplitudeIn (R := A) ((ModuleCat.derivedRestrictionOfScalars f).obj K) a b,
      ∀ q : PrimeSpectrum B,
        HasTorAmplitudeIn (R := f.sourceLocalRingAt q) (localizedAtPrime f K q) a b,
      ∀ m : MaximalSpectrum B,
        HasTorAmplitudeIn (R := f.sourceLocalRingAt m.toPrimeSpectrum)
          (localizedAtPrime f K m.toPrimeSpectrum) a b
    ] := sorry
/- Proof strategy: prove the TFAE cycle by localizing the derived tensor tests.  Global
Tor-amplitude localizes at every target prime, the all-prime condition restricts to maximal
ideals, and vanishing at every maximal localization reflects vanishing of the original homology
modules. -/

end HasTorAmplitudeIn
end CategoryTheory.DerivedCategory
