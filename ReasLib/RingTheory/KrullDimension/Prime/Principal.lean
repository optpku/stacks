/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.Cover
public import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.LTSeries
import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal Ideals and Weak Covers of Prime Ideals

@stack 00KV
-/

@[expose] public section

universe u

open Ideal

namespace PrimeSpectrum

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- A prime minimal over the sum of a prime and a principal ideal weakly covers the original
prime in the specialization order. -/
@[stacks 00KV "principal extensions of primes are weak covers"]
theorem wcovBy_of_isPrincipal_of_mem_minimalPrimes_sup
    {I : Ideal R} (hI : I.IsPrincipal) (p q : PrimeSpectrum R)
    (hq : q.asIdeal ∈ (p.asIdeal ⊔ I).minimalPrimes) :
    p ⩿ q := by
  obtain ⟨x, rfl⟩ := hI
  refine wcovBy_of_eq_or_eq (le_sup_left.trans hq.1.2) fun r hpr hrq ↦ ?_
  by_cases hpr' : r = p
  · exact Or.inl hpr'
  by_cases hrq' : r = q
  · exact Or.inr hrq'
  have hpr_lt : p < r := lt_of_le_of_ne hpr fun h ↦ hpr' h.symm
  have hrq_lt : r < q := lt_of_le_of_ne hrq hrq'
  have hxq : x ∈ q.asIdeal :=
    le_sup_right.trans hq.1.2 (mem_span_singleton_self x)
  obtain ⟨s, hxs, hps, hsq⟩ := exist_mem_one_of_mem_two hpr_lt hrq_lt hxq
  have hs_mem : p.asIdeal ⊔ span {x} ≤ s.asIdeal := by
    refine sup_le hps.le ?_
    exact (span_singleton_le_iff_mem s.asIdeal).2 hxs
  have hqs : q.asIdeal ≤ s.asIdeal := hq.2 ⟨s.isPrime, hs_mem⟩ hsq.le
  exact False.elim <| hsq.not_ge <| (asIdeal_le_asIdeal q s).1 hqs

end PrimeSpectrum
