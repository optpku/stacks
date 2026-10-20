/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Local semirings and localization

This leaf contains reusable localization facts whose hypotheses are intrinsic
to a local commutative semiring.

@stack 08HU
-/

universe u

namespace IsLocalRing

/-- A local commutative semiring is already the localization at the complement
of its maximal ideal.  The target determines the localization structure
canonically, so this is also the shared typeclass owner for downstream maps. -/
@[stacks 08HU "local ring as localization at the maximal ideal complement", instance]
theorem isLocalization_primeCompl_maximalIdeal
    {A : Type u} [CommSemiring A] [IsLocalRing A] :
    IsLocalization (maximalIdeal A).primeCompl A := sorry

end IsLocalRing
