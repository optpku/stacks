/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module

@[expose] public section

universe u

namespace associatedPrimesOfModule

/-- Over a Noetherian commutative ring, the exact associated primes of the quotient by
the intersection of two incomparable prime ideals are precisely those two ideals. -/
@[stacks 0CRA]
theorem quotient_inf_eq_pair {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : ¬ p ≤ q) (hqp : ¬ q ≤ p) :
    associatedPrimesOfModule R (R ⧸ (p ⊓ q)) = {p, q} :=
  sorry

end associatedPrimesOfModule
