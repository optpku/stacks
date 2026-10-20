/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import ReasLib.RingTheory.AdicCompletion.LocalMap
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Completed local rings at prime ideals

This file provides the completed local ring attached to a bundled prime and
the functorial map induced by a ring map and a prime lying above
it.  The global notation `R̂[p]` names the completed local ring and is shared
by the regularity and approximation APIs.
-/

open IsLocalRing

universe u v

namespace PrimeSpectrum

/-- The completion of the local ring `R_p` at its maximal ideal. -/
@[stacks 0CAR "completed local ring at a prime"]
abbrev CompletedLocalRing {R : Type u} [CommRing R] (p : PrimeSpectrum R) : Type u :=
  AdicCompletion (maximalIdeal (Localization.AtPrime p.asIdeal))
    (Localization.AtPrime p.asIdeal)

notation:max "R̂[" p "]" => PrimeSpectrum.CompletedLocalRing p

/-- Equality of bundled primes gives the ideal equality needed for the local
map between their localizations. -/
theorem comap_asIdeal_eq {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    p.asIdeal = Ideal.comap (algebraMap R S) q.asIdeal := sorry

/-- The canonical map on completed local rings induced by a ring map and a
prime of the target lying over the chosen source prime. -/
@[stacks 0CAR "map on completed local rings at primes"]
noncomputable abbrev completedLocalMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    CompletedLocalRing p →+* CompletedLocalRing q :=
  AdicCompletion.mapLocal
    (Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S)
      (comap_asIdeal_eq p q hq))

end PrimeSpectrum

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The map on completed local rings induced by an explicit ring homomorphism and a target
prime. This is the map-first adapter to `PrimeSpectrum.completedLocalMap`. -/
@[stacks 0CAR "map-first completed local map"]
noncomputable abbrev completedLocalMap (f : R →+* S) (q : PrimeSpectrum S) :
    PrimeSpectrum.CompletedLocalRing (PrimeSpectrum.comap f q) →+*
      PrimeSpectrum.CompletedLocalRing q :=
  AdicCompletion.mapLocal
    (Localization.localRingHom (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl)

end RingHom

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- An element outside a prime maps to a unit in the completion of the local ring
at that prime. -/
@[stacks 0CAR "unit in a completed local ring"]
theorem algebraMap_isUnit_atPrime_of_notMem (p : Ideal R) [p.IsPrime] {r : R} (hr : r ∉ p) :
    IsUnit (algebraMap R
      (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) r) := sorry

end AdicCompletion
