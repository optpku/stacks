/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.KrullDimension.Prime
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Noetherian Jacobson criteria

This file records criteria for establishing that a Noetherian ring is Jacobson from
prime-spectrum information, together with useful one-dimensional consequences.
-/

@[expose] public section

universe u

namespace IsJacobsonRing

/-- A Noetherian domain with infinitely many maximal ideals is Jacobson when every nonzero
prime ideal is maximal. -/
@[stacks 00G4 "nonzero primes are maximal"]
theorem of_nonzero_prime_isMaximal_of_infinite_maximalSpectrum
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Infinite (MaximalSpectrum R)]
    (hmax : ∀ ⦃P : Ideal R⦄, P ≠ ⊥ → P.IsPrime → P.IsMaximal) :
    IsJacobsonRing R := sorry

/-- A Noetherian domain of dimension at most one with infinitely many maximal ideals is
Jacobson. -/
@[stacks 00G4 "dimension-at-most-one companion"]
theorem of_dimensionLEOne_of_infinite_maximalSpectrum
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.DimensionLEOne R] [Infinite (MaximalSpectrum R)] :
    IsJacobsonRing R := sorry

/-- A Noetherian ring is Jacobson when every prime is maximal or has infinitely many strict
prime extensions above it. -/
@[stacks 00KX "Noetherian prime-over Jacobson criterion"]
theorem of_prime_isMaximal_or_infinite_primesOver
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hprime : ∀ p : PrimeSpectrum R,
      p.asIdeal.IsMaximal ∨ Infinite { q : PrimeSpectrum R // p ≤ q }) :
    IsJacobsonRing R := sorry

/-- A Noetherian domain of Krull dimension one with an infinite spectrum is Jacobson. -/
@[stacks 00KX "one-dimensional Jacobson criterion"]
theorem of_ringKrullDim_eq_one_of_infinite
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsDomain R] [Infinite (PrimeSpectrum R)] (hdim : ringKrullDim R = 1) :
    IsJacobsonRing R := sorry

end IsJacobsonRing

namespace Int

/-- The ring of integers is Jacobson. -/
@[stacks 00G4 "integers are Jacobson"]
instance instIsJacobsonRing : IsJacobsonRing ℤ := sorry

end Int
