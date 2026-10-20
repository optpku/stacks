/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.NonZeroDivisors
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.RingTheory.Localization.AtPrime.Map

/-!
# Finite-extension patching over two-dimensional local rings

This module records a patching theorem for finite extensions prescribed at the
nonclosed points of a principal zero locus.
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- Prescribed finite extensions at the nonclosed points of the zero locus of a
nonzerodivisor in a two-dimensional Noetherian local ring arise as the corresponding
localizations of one finite injective local extension with the same residue field, whose
cokernel is annihilated by a power of that nonzerodivisor. -/
theorem existsFiniteExtensionWithLocalizations
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) (t : A)
    (htm : t ∈ IsLocalRing.maximalIdeal A) (ht : t ∈ nonZeroDivisors A)
    {r : ℕ} (q : Fin r → PrimeSpectrum A) (hq_injective : Function.Injective q)
    (hq_ne_closedPoint : ∀ i, q i ≠ IsLocalRing.closedPoint A)
    (hV : PrimeSpectrum.zeroLocus ({t} : Set A) =
      Set.insert (IsLocalRing.closedPoint A) (Set.range q))
    (Bq : Fin r → Type u) [∀ i, CommRing (Bq i)]
    [∀ i, Algebra (Localization.AtPrime (q i).asIdeal) (Bq i)]
    [∀ i, Module.Finite (Localization.AtPrime (q i).asIdeal) (Bq i)]
    (hinjective : ∀ i, Function.Injective
      (algebraMap (Localization.AtPrime (q i).asIdeal) (Bq i)))
    (hann : ∀ i, Module.IsAnnihilatedByPower
      (Ideal.span
        ({algebraMap A (Localization.AtPrime (q i).asIdeal) t} :
          Set (Localization.AtPrime (q i).asIdeal)))
      (Bq i ⧸
        (Algebra.linearMap (Localization.AtPrime (q i).asIdeal) (Bq i)).range)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
        (_ : IsLocalRing C) (_ : IsLocalHom (algebraMap A C))
        (_ : Module.Finite A C) (_ : Function.Injective (algebraMap A C))
        (_ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap A C)))
        (e : ∀ i, Localization
          (Submonoid.map (algebraMap A C) (q i).asIdeal.primeCompl) ≃+* Bq i)
        (_ : ∀ i, (e i).toRingHom.comp
          (Localization.AtPrime.map (algebraMap A C) (q i).asIdeal) =
            algebraMap (Localization.AtPrime (q i).asIdeal) (Bq i)),
      Module.IsAnnihilatedByPower (Ideal.span ({t} : Set A))
        (C ⧸ (Algebra.linearMap A C).range) := sorry

end IsLocalRing

