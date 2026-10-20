/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified

@[expose] public section

/-!
# Reducedness Criteria for Analytically Unramified Local Rings

@stack 032Y

This leaf records reducedness and minimal-prime criteria for analytically
unramified Noetherian local rings.
-/

universe u

namespace IsAnalyticallyUnramified

/-- An analytically unramified Noetherian local ring is reduced. -/
@[stacks 032Y "(1)"]
theorem isReduced {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAnalyticallyUnramified R] :
    IsReduced R := sorry

/-- The quotient by a minimal prime of an analytically unramified Noetherian
local ring is analytically unramified. -/
@[stacks 032Y "(2)"]
theorem minimalPrime {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAnalyticallyUnramified R] (p : PrimeSpectrum R)
    (hp : p.asIdeal ∈ minimalPrimes R) :
    IsAnalyticallyUnramified (R ⧸ p.asIdeal) := sorry

/-- A reduced Noetherian local ring is analytically unramified when each
quotient by a minimal prime is analytically unramified. -/
@[stacks 032Y "(3)"]
theorem of_isReduced_of_minimalPrimes {R : Type u}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R]
    (h_minimal : ∀ p : PrimeSpectrum R, p.asIdeal ∈ minimalPrimes R →
      IsAnalyticallyUnramified (R ⧸ p.asIdeal)) :
    IsAnalyticallyUnramified R := sorry

end IsAnalyticallyUnramified
