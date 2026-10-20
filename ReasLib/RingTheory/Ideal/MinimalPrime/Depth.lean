/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Depth and dimension at minimal primes

This file records the depth-zero and dimension-zero consequences of localizing
a Noetherian commutative ring at one of its minimal primes.
-/

@[expose] public section

universe u

open scoped ENat

namespace IsMinimalPrime

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {p : Ideal R} [p.IsPrime]

/-- The module depth of a Noetherian ring localized at a minimal prime is zero. -/
theorem moduleDepth_atPrime_eq_zero (hp : IsMinimalPrime p) :
    moduleDepth (Localization.AtPrime p) (Localization.AtPrime p) = 0 := sorry

/-- The Krull dimension of a Noetherian ring localized at a minimal prime is zero. -/
theorem ringKrullDim_atPrime_eq_zero (hp : IsMinimalPrime p) :
    ringKrullDim (Localization.AtPrime p) = 0 := sorry

end IsMinimalPrime
