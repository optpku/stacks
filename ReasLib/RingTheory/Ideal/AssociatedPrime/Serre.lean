/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded

@[expose] public section

/-!
# Serre's condition and embedded associated primes

For a finite module over a Noetherian ring, Serre's condition `(S_1)` is
equivalent to the absence of embedded associated primes.
-/

universe u v

namespace Module

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A finite module over a Noetherian ring has no embedded associated primes if
and only if it satisfies Serre's condition `(S_1)`. -/
@[stacks 031Q "embedded associated primes and Serre S1"]
theorem embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one :
    embeddedAssociatedPrimes R M = ∅ ↔ Module.SerreConditionS R M 1 := sorry

end Module
