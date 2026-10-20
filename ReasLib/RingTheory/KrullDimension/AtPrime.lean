/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.KrullDimension.DimensionLEOne

/-!
# Dimension-one prime localizations

This leaf records the elementary height-one consequences of a `Ring.DimensionLEOne` domain.
The declarations are phrased at the ideal and prime-spectrum owners so later localization and
valuation arguments can reuse them without importing a chapter file.
-/

@[expose] public section

universe u

namespace Ring.DimensionLEOne

/-- A nonzero prime in a domain of dimension at most one has prime height one. -/
@[stacks 00PH "height one for nonzero primes in dimension at most one"]
theorem height_eq_one_of_ne_bot
    {A : Type u} [CommRing A] [IsDomain A] [Ring.DimensionLEOne A]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥) :
    p.height = 1 := sorry

end Ring.DimensionLEOne

namespace IsLocalization.AtPrime

/-- Localizing a dimension-at-most-one domain at a nonzero prime has Krull dimension one. -/
@[stacks 00PH "dimension one of a nonzero prime localization"]
theorem ringKrullDim_eq_one_of_dimensionLEOne_of_ne_bot
    {A : Type u} [CommRing A] [IsDomain A] [Ring.DimensionLEOne A]
    (p : PrimeSpectrum A) (hp : p.asIdeal ≠ ⊥) :
    ringKrullDim (Localization.AtPrime p.asIdeal) = 1 := sorry

end IsLocalization.AtPrime

end
