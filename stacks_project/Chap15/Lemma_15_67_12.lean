/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.Restriction
import StacksCheckRecall

/-!
# Lemma 15.67.12

@stack 066K

The reusable theorem is stated for an explicit ring homomorphism and its canonical target module.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 15.67.12: restriction across a map of Tor dimension at most `d` lowers the
Tor-amplitude bound by `d`. -/
@[stacks 066K "Lemma 15.67.12"]
#check fun {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (K : DerivedCategory (ModuleCat B)) (a b : ℤ) (d : ℕ)
    (hf : ModuleCat.HasTorDimensionLE (R := A) f.targetModule d)
    (hK : DerivedCategory.HasTorAmplitudeIn (R := B) K a b) ↦
  (DerivedCategory.HasTorAmplitudeIn.restrictScalars_of_torDimensionLE f K hf hK :
    DerivedCategory.HasTorAmplitudeIn (R := A)
      ((ModuleCat.derivedRestrictionOfScalars f).obj K) (a - (d : ℤ)) b)
