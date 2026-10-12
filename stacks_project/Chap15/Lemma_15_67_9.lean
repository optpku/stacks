/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.Homology

/-!
# Lemma 15.67.9

@stack 066I

The source is stated for rings.  This recall records the current commutative-ring specialization
used by the ModuleCat derived tensor API.  The owner exposes both the literal intervals
`[a - i, b - i]` on `Hⁱ(K)[0]` and the equivalent common interval `[a, b]` on
`ShiftedCohomology.family`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 15.67.9 (066I) (1): bounded Tor-amplitude from the source-indexed cohomology
intervals. -/
@[stacks 066I "bounded Tor-amplitude from source-indexed cohomology intervals"]
#check fun {R : Type u} [CommRing R] (a b : ℤ)
    (K : DerivedCategory.Bounded (ModuleCat R))
    (hAmplitude : ∀ i : ℤ, DerivedCategory.HasTorAmplitudeIn R
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj
        ((DerivedCategory.Bounded.homologyFunctor (ModuleCat R) i).obj K))
      (a - i) (b - i)) ↦
  (DerivedCategory.HasTorAmplitudeIn.of_bounded_of_homology a b K hAmplitude :
    DerivedCategory.HasTorAmplitudeIn R K.obj a b)

/- Lemma 15.67.9 (066I) (2): bounded cohomology of finite Tor dimension. -/
@[stacks 066I "finite Tor dimension from bounded cohomology"]
#check fun {R : Type u} [CommRing R] (K : DerivedCategory.Bounded (ModuleCat R))
    (hFinite : ∀ i : ℤ, ModuleCat.HasFiniteTorDimension R
      ((DerivedCategory.Bounded.homologyFunctor (ModuleCat R) i).obj K)) ↦
  (DerivedCategory.HasFiniteTorDimension.of_bounded_of_homology K hFinite :
    DerivedCategory.HasFiniteTorDimension R K.obj)

/- Shift, finite-support induction, and lower-truncation ingredients exposed by the owners. -/
#check @DerivedCategory.hasTorAmplitudeIn_single_iff
#check @DerivedCategory.HasTorAmplitudeIn.of_isGE_isLE_of_shiftedCohomology
#check @DerivedCategory.HasTorAmplitudeIn.of_bounded_of_shiftedCohomology
#check @DerivedCategory.TruncGE.homologyIso
