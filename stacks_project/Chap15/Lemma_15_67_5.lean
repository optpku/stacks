/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude.Triangulated

@[expose] public section

/-!
# Lemma 15.67.5

@stack 0655
-/

open CategoryTheory
open CategoryTheory.Pretriangulated

universe u

/- Lemma 15.67.5 (1): Tor-amplitude propagates to the third vertex of a distinguished
triangle. -/
@[stacks 0655 "Lemma 15.67.5 (1)"]
#check fun {R : Type u} [CommRing R] (T : Triangle (DerivedCategory (ModuleCat R)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat R))) (a b : ℤ)
    (h₁ : DerivedCategory.HasTorAmplitudeIn R T.obj₁ (a + 1) (b + 1))
    (h₂ : DerivedCategory.HasTorAmplitudeIn R T.obj₂ a b) ↦
  (DerivedCategory.DerivedTensor.TorAmplitude.obj₃_of_distinguished T hT h₁ h₂ :
    DerivedCategory.HasTorAmplitudeIn R T.obj₃ a b)

/- Lemma 15.67.5 (2): Tor-amplitude propagates to the middle vertex of a distinguished
triangle. -/
@[stacks 0655 "Lemma 15.67.5 (2)"]
#check fun {R : Type u} [CommRing R] (T : Triangle (DerivedCategory (ModuleCat R)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat R))) (a b : ℤ)
    (h₁ : DerivedCategory.HasTorAmplitudeIn R T.obj₁ a b)
    (h₃ : DerivedCategory.HasTorAmplitudeIn R T.obj₃ a b) ↦
  (DerivedCategory.DerivedTensor.TorAmplitude.obj₂_of_distinguished T hT h₁ h₃ :
    DerivedCategory.HasTorAmplitudeIn R T.obj₂ a b)

/- Lemma 15.67.5 (3): Tor-amplitude propagates to the first vertex of a distinguished
triangle. -/
@[stacks 0655 "Lemma 15.67.5 (3)"]
#check fun {R : Type u} [CommRing R] (T : Triangle (DerivedCategory (ModuleCat R)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat R))) (a b : ℤ)
    (h₂ : DerivedCategory.HasTorAmplitudeIn R T.obj₂ (a + 1) (b + 1))
    (h₃ : DerivedCategory.HasTorAmplitudeIn R T.obj₃ a b) ↦
  (DerivedCategory.DerivedTensor.TorAmplitude.obj₁_of_distinguished T hT h₂ h₃ :
    DerivedCategory.HasTorAmplitudeIn R T.obj₁ (a + 1) (b + 1))

/- Shifts translate Tor-amplitude intervals and preserve finite Tor dimension. -/
#check @DerivedCategory.DerivedTensor.hasTorAmplitudeIn_shift_iff
#check @DerivedCategory.DerivedTensor.hasFiniteTorDimension_shift_iff
