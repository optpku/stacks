/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.LocalizationAway
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.67.16

@stack 066N

This chapter entry recalls the reusable localization-away Tor-amplitude criterion.
-/

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory

/- Lemma 15.67.16: the chapter recalls the canonical finite localization-away Tor-amplitude
criterion from the shared owner. -/
@[stacks 066N "Lemma 15.67.16"]
#check fun {R : Type u} [CommRing R] {ι : Type*} [Finite ι]
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ)
    (hloc : ∀ i,
      DerivedCategory.HasTorAmplitudeIn (R := Localization.Away (f i))
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap R (Localization.Away (f i)))).obj K) a b) ↦
  (DerivedCategory.HasTorAmplitudeIn.of_finite_localizationAway f hunit K a b hloc :
    DerivedCategory.HasTorAmplitudeIn (R := R) K a b)

end CategoryTheory
