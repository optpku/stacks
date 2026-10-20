/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

@[expose] public section

universe u v

namespace RingHom

/-- A finite injective ring homomorphism from a local commutative ring has a prime
ideal in the target whose contraction is the maximal ideal of the source. -/
theorem exists_comap_eq_maximalIdeal_of_finite {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] {f : A →+* B} (hf : f.Finite)
    (hinj : Function.Injective f) :
    ∃ q : Ideal B, q.IsPrime ∧ q.comap f = IsLocalRing.maximalIdeal A :=
  sorry

end RingHom
