/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor amplitude under derived scalar extension

@stack 066L
@stack 068S
@stack 0DJF
@stack 0H75
@stack 0DJG

This leaf states scalar-extension stability using an explicit ring homomorphism. Keeping the map
explicit makes the API independent of downstream `Algebra` instances and tensor notation.
The rings share a universe because the current standard-universe `HasTorAmplitudeIn` surface does
not accept the universe-raised target produced by cross-universe scalar extension.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Stacks `066L`: derived extension of scalars preserves a fixed Tor-amplitude interval. -/
@[stacks 066L "Tor amplitude under derived scalar extension"]
theorem HasTorAmplitudeIn.extension
    {K : DerivedCategory (ModuleCat R)} {a b : ℤ}
    (hK : HasTorAmplitudeIn R K a b) (σ : R →+* S) :
    HasTorAmplitudeIn S ((ModuleCat.derivedExtensionOfScalars σ).obj K) a b := sorry
/- Proof strategy: identify every `S`-linear tensor test of the scalar extension with the
corresponding `R`-linear tensor test by derived-tensor associativity, then reuse the original
homological support bound. -/

/-- Lemma 15.67.17 (068S): faithfully flat derived scalar extension reflects a fixed
Tor-amplitude interval. -/
@[stacks 068S "faithfully flat Tor-amplitude reflection"]
theorem HasTorAmplitudeIn.of_faithfullyFlat
    (σ : R →+* S) (hσ : σ.FaithfullyFlat)
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ)
    (hK : HasTorAmplitudeIn S
      ((ModuleCat.derivedExtensionOfScalars σ).obj K) a b) :
    HasTorAmplitudeIn R K a b := sorry
/- Proof strategy: base-change each degree-zero tensor test along `σ`; faithful flatness
reflects zero homology modules, so the vanishing outside `[a, b]` descends to `R`. -/

/-- Lemma 15.67.18 (0DJF): in a scalar tower, faithfully flat base change preserves the
Tor-amplitude of an object measured over the base ring.  The bundled restriction functors keep
the exactness data explicit and avoid chapter-local instance reconstruction. -/
@[stacks 0DJF "relative Tor-amplitude under faithfully flat base change"]
theorem HasTorAmplitudeIn.iff_of_faithfullyFlat_baseChange
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (K : DerivedCategory (ModuleCat A)) (a b : ℤ)
    (hσ : (algebraMap A B).FaithfullyFlat) :
    HasTorAmplitudeIn R
        (((ModuleCat.RestrictScalars.exact (algebraMap R A)).mapDerivedCategory).obj K) a b ↔
      HasTorAmplitudeIn R
        (((ModuleCat.RestrictScalars.exact (algebraMap R B)).mapDerivedCategory).obj
          ((ModuleCat.derivedExtensionOfScalars (algebraMap A B)).obj K)) a b := sorry
/- Proof strategy: use the scalar-tower comparison between the two restricted derived tensor
tests; ascent follows from `HasTorAmplitudeIn.extension`, and descent follows from
`HasTorAmplitudeIn.of_faithfullyFlat`. -/

/-- Finite Tor dimension is preserved by derived extension of scalars. -/
@[stacks 066L "finite Tor dimension under derived scalar extension"]
theorem HasFiniteTorDimension.extension
    {K : DerivedCategory (ModuleCat R)}
    (hK : HasFiniteTorDimension R K) (σ : R →+* S) :
    HasFiniteTorDimension S ((ModuleCat.derivedExtensionOfScalars σ).obj K) := sorry
/- Proof strategy: choose an interval witnessing `hK`, preserve that interval with
`HasTorAmplitudeIn.extension`, and repackage it as finite Tor dimension. -/

/-- Tor-amplitude is reflected by derived scalar extension along a surjective homomorphism with
nilpotent kernel.  Keeping `σ` explicit makes the criterion independent of algebra instances and
is the reusable owner behind the nilpotent-thickening arguments of Lemmas 15.67.20 and 15.85.8. -/
@[stacks 0H75 "Tor amplitude across a nilpotent thickening"]
theorem HasTorAmplitudeIn.extension_iff_of_surjective_of_nilpotent_ker
    (σ : R →+* S) (hσ : Function.Surjective σ)
    (hker : IsNilpotent (RingHom.ker σ))
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ) :
    HasTorAmplitudeIn S ((ModuleCat.derivedExtensionOfScalars σ).obj K) a b ↔
      HasTorAmplitudeIn R K a b := sorry
/- Proof strategy: the reverse implication is scalar-extension stability.  For the forward,
identify `S` with the quotient by `RingHom.ker σ` and use the finite nilpotence filtration to
reflect vanishing of each tensor-test homology module. -/

/-- Finite Tor dimension is likewise reflected by a surjective nilpotent scalar extension. -/
@[stacks 0DJG "finite Tor dimension across a nilpotent thickening"]
theorem HasFiniteTorDimension.extension_iff_of_surjective_of_nilpotent_ker
    (σ : R →+* S) (hσ : Function.Surjective σ)
    (hker : IsNilpotent (RingHom.ker σ))
    (K : DerivedCategory (ModuleCat R)) :
    HasFiniteTorDimension S ((ModuleCat.derivedExtensionOfScalars σ).obj K) ↔
      HasFiniteTorDimension R K := sorry
/- Proof strategy: transport a witnessing interval in each direction using
`HasTorAmplitudeIn.extension_iff_of_surjective_of_nilpotent_ker`. -/

end CategoryTheory.DerivedCategory
