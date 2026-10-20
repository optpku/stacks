/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Krull dimension of a principal quotient

The reusable core is stated for an element of the Jacobson radical.  The local-ring results are
specializations obtained by replacing the Jacobson radical with the maximal ideal.
-/

@[expose] public section

universe u

open IsLocalRing

variable {R : Type u} [CommRing R]

/-- Lemma 10.60.13 (global Jacobson companion; Stacks tag 00KW): quotienting a Noetherian ring by
an element of its Jacobson radical lowers Krull dimension by at most one. -/
@[stacks 00KW "Jacobson-radical dimension bound"]
theorem ringKrullDim_le_ringKrullDim_quotient_span_singleton_succ_of_mem_jacobson
    [IsNoetherianRing R] {x : R} (hx : x ∈ Ring.jacobson R) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := sorry

/-- Lemma 10.60.13 (minimal-prime companion; Stacks tag 00KW): if `x` avoids every minimal prime,
the principal quotient has Krull dimension at most one less than that of the original ring. -/
@[stacks 00KW "minimal-prime dimension bound"]
theorem ringKrullDim_quotient_span_singleton_succ_le_ringKrullDim_of_notMem_minimalPrimes
    {x : R} (hmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 ≤ ringKrullDim R := sorry

/-- Lemma 10.60.13 (global equality companion; Stacks tag 00KW): a Jacobson-radical element
avoiding every minimal prime lowers Krull dimension by exactly one. -/
@[stacks 00KW "Jacobson-radical equality case"]
theorem
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_notMem_minimalPrimes_of_mem_jacobson
    [IsNoetherianRing R] {x : R} (hmin : ∀ p ∈ minimalPrimes R, x ∉ p)
    (hx : x ∈ Ring.jacobson R) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := sorry

/-- Lemma 10.60.13 (1), canonical local owner: in a Noetherian local ring, quotienting by an
element of the maximal ideal lowers Krull dimension by at most one. -/
@[stacks 00KW "local-ring dimension bound"]
theorem ringKrullDim_le_ringKrullDim_quotient_span_singleton_succ
    [IsNoetherianRing R] [IsLocalRing R] {x : R} (hx : x ∈ maximalIdeal R) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := sorry

/-- Lemma 10.60.13 (2), canonical local owner: in a Noetherian local ring, an element of the
maximal ideal avoiding every minimal prime lowers Krull dimension by exactly one. -/
@[stacks 00KW "local-ring equality case"]
theorem ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_notMem_minimalPrimes
    [IsNoetherianRing R] [IsLocalRing R] {x : R}
    (hmin : ∀ p ∈ minimalPrimes R, x ∉ p) (hx : x ∈ maximalIdeal R) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := sorry
