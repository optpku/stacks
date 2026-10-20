/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.NonZeroDivisors
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

/-!
# Power factorization bounds in one-dimensional local rings
-/

@[expose] public section

universe u v

namespace IsLocalRing.DimensionOne

/-- For nonzerodivisors `a` and `b` in a one-dimensional Noetherian local ring,
with `a` in the maximal ideal, the exponent in any factorization of `b` by a power
of `a` in a finite injective ring extension is uniformly bounded. -/
theorem existsPowerFactorizationBound
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) (a b : R)
    (ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R)
    (ha_mem : a ∈ IsLocalRing.maximalIdeal R) :
    ∃ n : ℕ, ∀ {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S],
      Function.Injective (algebraMap R S) → ∀ m : ℕ,
        (algebraMap R S a) ^ m ∣ algebraMap R S b → m ≤ n := sorry

end IsLocalRing.DimensionOne
