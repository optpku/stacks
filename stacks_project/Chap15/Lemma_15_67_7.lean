module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude.Retracts

@[expose] public section

/-!
# Lemma 15.67.7

@stack 066G
-/

open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 15.67.7: both summands of a biproduct inherit its Tor-amplitude interval. -/
@[stacks 066G]
#check fun {R : Type u} [CommRing R] (K L : DerivedCategory (ModuleCat R)) (a b : ℤ)
    (hKL : DerivedCategory.HasTorAmplitudeIn R (K ⊞ L) a b) ↦
  (DerivedCategory.DerivedTensor.TorAmplitude.summands_of_biprod K L hKL :
    DerivedCategory.HasTorAmplitudeIn R K a b ∧
      DerivedCategory.HasTorAmplitudeIn R L a b)

/- The two projections of Lemma 15.67.7 are available separately for downstream use. -/
#check @DerivedCategory.DerivedTensor.TorAmplitude.left_of_biprod
#check @DerivedCategory.DerivedTensor.TorAmplitude.right_of_biprod
