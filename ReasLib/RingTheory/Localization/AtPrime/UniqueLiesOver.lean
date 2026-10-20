/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.Topology.Inseparable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Prime localization from a unique prime above the base

This leaf identifies localization at a base prime with localization at the
unique prime above it, under either going up or the corresponding going-down
uniqueness hypothesis.

@stack 00EA
-/

@[expose] public section

universe u v

namespace IsLocalization.AtPrime

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime] [q.LiesOver p]

/-- Lemma 10.41.11, going-up case: if `q` is the unique prime of `S`
above `p`, then localizing `S` away from `p` is localization at `q`. -/
@[stacks 00EA "going-up case"]
theorem of_unique_liesOver_of_goingUp
    (hgu : SpecializingMap (PrimeSpectrum.comap (algebraMap R S)))
    (hunique : Subsingleton (p.primesOver S)) :
    IsLocalization.AtPrime
      (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) q := sorry

/-- Lemma 10.41.11, going-down case: if primes above every base prime are
unique, then localizing `S` away from `p` is localization at `q`. -/
@[stacks 00EA "going-down case"]
theorem of_unique_liesOver_of_goingDown
    [Algebra.HasGoingDown R S]
    (hunique : ∀ p' : Ideal R, p'.IsPrime → Subsingleton (p'.primesOver S)) :
    IsLocalization.AtPrime
      (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) q := sorry

end IsLocalization.AtPrime
