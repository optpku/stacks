/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import ReasLib.RingTheory.KrullDimension.HeightOne
public import ReasLib.RingTheory.Localization.FractionRing.HeightOne.Unit
public import ReasLib.RingTheory.LocalRing.TameSymbol.Determinant

/-!
# Tame symbols at height-one primes

This file defines the local tame-symbol value and its integer order at a height-one prime.
-/

@[expose] public section

noncomputable section

universe u v

namespace TameSymbol

/-- The tame symbol at a height-one point, transported canonically from an arbitrary chosen
fraction-field model to `FractionRing A`. -/
noncomputable def valueAt
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (p : PrimeSpectrum.HeightOne A) (f g : Kˣ) : p.asIdeal.ResidueFieldˣ :=
  TameSymbol.value (Localization.AtPrime p.asIdeal) (FractionRing A)
    ((IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
      (Localization.AtPrime p.asIdeal)).trans
        (congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) p.asIdeal_height))
    ((Units.mapEquiv (FractionRing.algEquiv A K).toMulEquiv).symm f)
    ((Units.mapEquiv (FractionRing.algEquiv A K).toMulEquiv).symm g)

/-- `valueAt` is evaluation of the local tame symbol after canonical transport to
`FractionRing A`. -/
theorem valueAt_def
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (p : PrimeSpectrum.HeightOne A) (f g : Kˣ) :
    valueAt A K p f g =
      TameSymbol.value (Localization.AtPrime p.asIdeal) (FractionRing A)
        ((IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
          (Localization.AtPrime p.asIdeal)).trans
            (congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) p.asIdeal_height))
        ((Units.mapEquiv (FractionRing.algEquiv A K).toMulEquiv).symm f)
        ((Units.mapEquiv (FractionRing.algEquiv A K).toMulEquiv).symm g) := sorry

/-- If both arguments are units at a height-one point, their local tame symbol is one. -/
theorem valueAt_eq_one_of_isUnitAt
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (p : PrimeSpectrum.HeightOne A) (f g : Kˣ)
    (hf : p.IsUnitAt K f) (hg : p.IsUnitAt K g) : valueAt A K p f g = 1 := sorry

/-- The integer order of the local tame symbol in the residue field of a height-one prime. -/
noncomputable def orderAt
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hdim : ringKrullDim A = 2) (p : PrimeSpectrum.HeightOne A) (f g : Kˣ) : ℤ :=
  -- Local instance justification (proof-local temporary data): `hdim` and the height-one condition give the quotient-dimension bound required by `Ring.ordFrac` here.
  letI : Ring.KrullDimLE 1 (A ⧸ p.asIdeal) :=
    (Ring.krullDimLE_iff).2 ((p.quotientKrullDim_eq_one hdim).le.trans_eq rfl)
  WithZero.log (Ring.ordFrac (A ⧸ p.asIdeal) (valueAt A K p f g : p.asIdeal.ResidueField))

/-- `orderAt` is `WithZero.log` applied to the order of vanishing of the local tame symbol. -/
theorem orderAt_def
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hdim : ringKrullDim A = 2) (p : PrimeSpectrum.HeightOne A) (f g : Kˣ) :
    orderAt A K hdim p f g =
      -- Local instance justification (proof-local temporary data): `hdim` and the height-one condition give the quotient-dimension bound required by `Ring.ordFrac` here.
      letI : Ring.KrullDimLE 1 (A ⧸ p.asIdeal) :=
        (Ring.krullDimLE_iff).2 ((p.quotientKrullDim_eq_one hdim).le.trans_eq rfl)
      WithZero.log
        (Ring.ordFrac (A ⧸ p.asIdeal) (valueAt A K p f g : p.asIdeal.ResidueField)) := sorry

/-- If both arguments are units at a height-one point, the order of their local tame symbol
is zero. -/
theorem orderAt_eq_zero_of_isUnitAt
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hdim : ringKrullDim A = 2) (p : PrimeSpectrum.HeightOne A) (f g : Kˣ)
    (hf : p.IsUnitAt K f) (hg : p.IsUnitAt K g) : orderAt A K hdim p f g = 0 := sorry

/-- Only finitely many height-one points contribute a nonzero order to the local tame
symbols of two fixed fraction-field units. -/
theorem orderAt_hasFiniteSupport
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hdim : ringKrullDim A = 2) (f g : Kˣ) :
    Function.HasFiniteSupport
      (fun p : PrimeSpectrum.HeightOne A ↦ orderAt A K hdim p f g) := sorry

end TameSymbol
