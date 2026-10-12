/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.ResidueField
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import ReasLib.RingTheory.GlobalDimension.Basic
public import ReasLib.RingTheory.RegularLocalRing.GlobalDimension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfectness from fiberwise homological dimension

@stack 068X
@stack 09PC

Flat maps whose fibers have uniformly bounded global dimension transfer a restricted
Tor-amplitude bound to a perfect complex over the target. The local regular-fiber criterion is
the closed-fiber specialization.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing

universe u

-- Local instance justification (search instability): derived restriction and homology use the
-- standard t-structure on derived categories of modules.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-- Lemma 15.78.5 (068X): for a flat map `A ⟶ B` whose fibers have global dimension at most
`d`, a pseudo-coherent `B`-complex of restricted Tor-amplitude `[a, b]` is perfect over `B` with
Tor-amplitude `[a - d, b]`. -/
@[stacks 068X "fiberwise global dimension shifts Tor amplitude"]
theorem isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_restrictScalars_of_fiber_hasGlobalDimensionLE
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (K : DerivedCategory (ModuleCat B)) (a b : ℤ) (d : ℕ)
    (hfiber : ∀ p : PrimeSpectrum A, HasGlobalDimensionLE (p.asIdeal.Fiber B) d)
    (hKpc : K.IsPseudoCoherent)
    (hKamp : DerivedCategory.HasTorAmplitudeIn (R := A)
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K) a b) :
    K.IsPerfect ∧
      DerivedCategory.HasTorAmplitudeIn (R := B) K (a - (d : ℤ)) b := sorry

/-- Lemma 15.78.6 (1) (09PC): for a flat local map with regular closed fiber of dimension `d`,
closed-fiber homology concentrated in `[a, b]` implies perfectness over the target and
Tor-amplitude `[a - d, b]`. -/
@[stacks 09PC "regular closed fiber and residue-field homology"]
theorem isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_baseResidueFieldDerivedHomology_vanishing_of_closedFiber_isRegularLocalRing
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (K : DerivedCategory (ModuleCat B)) (a b : ℤ) (d : ℕ)
    [IsRegularLocalRing ((maximalIdeal A).Fiber B)]
    (hdim : ringKrullDim ((maximalIdeal A).Fiber B) = d)
    (hKpc : K.IsPseudoCoherent)
    (hKκ : ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero
        (DerivedCategory.PrimeResidueField.homology (closedPoint A)
          ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K) i)) :
    K.IsPerfect ∧
      DerivedCategory.HasTorAmplitudeIn (R := B) K (a - (d : ℤ)) b := sorry

/-- Lemma 15.78.6 (2) (09PC): the same regular closed-fiber conclusion follows from
Tor-amplitude `[a, b]` after restriction of scalars to the source. -/
@[stacks 09PC "regular closed fiber and restricted Tor amplitude"]
theorem isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_restrictScalars_of_closedFiber_isRegularLocalRing
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (K : DerivedCategory (ModuleCat B)) (a b : ℤ) (d : ℕ)
    [IsRegularLocalRing ((maximalIdeal A).Fiber B)]
    (hdim : ringKrullDim ((maximalIdeal A).Fiber B) = d)
    (hKpc : K.IsPseudoCoherent)
    (hKamp : DerivedCategory.HasTorAmplitudeIn (R := A)
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K) a b) :
    K.IsPerfect ∧
      DerivedCategory.HasTorAmplitudeIn (R := B) K (a - (d : ℤ)) b := sorry

end CategoryTheory
