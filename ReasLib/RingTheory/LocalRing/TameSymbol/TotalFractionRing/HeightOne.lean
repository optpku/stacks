module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import ReasLib.RingTheory.KrullDimension.HeightOne
public import ReasLib.RingTheory.LocalRing.TameSymbol.TotalFractionRing

@[expose] public section

/-!
# Orders of integral tame symbols at height-one primes

This module localizes integral nonzerodivisors at height-one primes and records the
order of the resulting integral tame symbol in the fraction field of the prime quotient.
-/

noncomputable section

open scoped BigOperators nonZeroDivisors

universe u

namespace TameSymbol.Total

/-- The localization map sends a nonzerodivisor to a nonzerodivisor at a height-one
prime. -/
def mapNonzeroAt {A : Type u} [CommRing A] (p : PrimeSpectrum.HeightOne A) :
    A⁰ →* (Localization.AtPrime p.asIdeal)⁰ :=
  ((algebraMap A (Localization.AtPrime p.asIdeal)).toMonoidHom.restrict A⁰).codRestrict
    (Localization.AtPrime p.asIdeal)⁰ fun a ↦
      IsLocalization.nonZeroDivisors_le_comap p.asIdeal.primeCompl
        (Localization.AtPrime p.asIdeal) a.property

/-- The element underlying `mapNonzeroAt p a` is the localization of `a`. -/
theorem coe_mapNonzeroAt_apply {A : Type u} [CommRing A]
    (p : PrimeSpectrum.HeightOne A) (a : A⁰) :
    (mapNonzeroAt p a : Localization.AtPrime p.asIdeal) =
      algebraMap A (Localization.AtPrime p.asIdeal) a := sorry

/-- The integral tame symbol of two nonzerodivisors after localization at a height-one
prime. -/
noncomputable def integralValueAt {A : Type u} [CommRing A] [IsNoetherianRing A]
    (p : PrimeSpectrum.HeightOne A) (a b : A⁰) : p.asIdeal.ResidueFieldˣ :=
  integralValue (Localization.AtPrime p.asIdeal)
    ((IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
      (Localization.AtPrime p.asIdeal)).trans
        (congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) p.asIdeal_height))
    (mapNonzeroAt p a) (mapNonzeroAt p b)

/-- `integralValueAt` is the integral tame symbol evaluated on the localized
nonzerodivisors. -/
theorem integralValueAt_def {A : Type u} [CommRing A] [IsNoetherianRing A]
    (p : PrimeSpectrum.HeightOne A) (a b : A⁰) :
    integralValueAt p a b =
      integralValue (Localization.AtPrime p.asIdeal)
        ((IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
          (Localization.AtPrime p.asIdeal)).trans
            (congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) p.asIdeal_height))
        (mapNonzeroAt p a) (mapNonzeroAt p b) := sorry

/-- The integer order over the prime quotient of the local integral tame symbol. -/
noncomputable def orderAt
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) (p : PrimeSpectrum.HeightOne A) (a b : A⁰) : ℤ :=
  -- Local instance justification (proof-local temporary data): `hdim` and the height-one condition give the quotient-dimension bound required by `Ring.ordFrac` here.
  letI : Ring.KrullDimLE 1 (A ⧸ p.asIdeal) :=
    (Ring.krullDimLE_iff).2 ((p.quotientKrullDim_eq_one hdim).le.trans_eq rfl)
  WithZero.log
    (Ring.ordFrac (A ⧸ p.asIdeal) (integralValueAt p a b : p.asIdeal.ResidueField))

/-- `orderAt` is `WithZero.log` applied to the order of vanishing over the prime
quotient. -/
theorem orderAt_def
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) (p : PrimeSpectrum.HeightOne A) (a b : A⁰) :
    orderAt A hdim p a b =
      -- Local instance justification (proof-local temporary data): `hdim` and the height-one condition give the quotient-dimension bound required by `Ring.ordFrac` here.
      letI : Ring.KrullDimLE 1 (A ⧸ p.asIdeal) :=
        (Ring.krullDimLE_iff).2 ((p.quotientKrullDim_eq_one hdim).le.trans_eq rfl)
      WithZero.log
        (Ring.ordFrac (A ⧸ p.asIdeal)
          (integralValueAt p a b : p.asIdeal.ResidueField)) := sorry

/-- If both nonzerodivisors become units at a height-one prime, the order of their local
integral tame symbol is zero. -/
theorem orderAt_eq_zero_of_isUnit
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) (p : PrimeSpectrum.HeightOne A) (a b : A⁰)
    (ha : IsUnit (algebraMap A (Localization.AtPrime p.asIdeal) a))
    (hb : IsUnit (algebraMap A (Localization.AtPrime p.asIdeal) b)) :
    orderAt A hdim p a b = 0 := sorry

/-- Only finitely many height-one primes contribute a nonzero order for two fixed
nonzerodivisors. -/
theorem orderAt_hasFiniteSupport
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) (a b : A⁰) :
    Function.HasFiniteSupport
      (fun p : PrimeSpectrum.HeightOne A ↦ orderAt A hdim p a b) := sorry

end TameSymbol.Total
