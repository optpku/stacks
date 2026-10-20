/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Henselianity and the closed subset of an ideal

The henselian-pair predicate depends only on the closed subset cut out by the ideal in the prime
spectrum.  This is the source-facing radical-invariance bridge; the idempotent comparison used in
its proof remains an implementation detail of the canonical henselian criterion.

@stack 09XJ
-/

@[expose] public section

universe u

/-- Lemma 15.11.7 (09XJ): ideals with the same prime-spectrum zero locus define henselian pairs
simultaneously. -/
@[stacks 09XJ "henselianity depends only on the ideal zero locus"]
theorem henselianRing_iff_of_zeroLocus_eq
    {A : Type u} [CommRing A] (I J : Ideal A)
    (hV : PrimeSpectrum.zeroLocus (I : Set A) = PrimeSpectrum.zeroLocus (J : Set A)) :
    HenselianRing A I ↔ HenselianRing A J := sorry
-- Proof strategy: convert `hV` to equality of radicals, show idempotent lifting is unchanged
-- after quotienting by the nilpotent radical kernel, and compare both henselian-pair predicates
-- through Mathlib's canonical idempotent/Gabber-root criterion.
