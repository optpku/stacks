/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.Algebra.CharP.Frobenius

@[expose] public section

universe u

/-- In a Noetherian commutative ring of prime characteristic, regularity is
equivalent to flatness of the prime-power Frobenius endomorphism. -/
theorem isRegularRing_iff_frobenius_flat
    (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hp : (p : A) = 0) :
    IsRegularRing A ↔ (RingHom.frobeniusOfPrime p hp).Flat := sorry
