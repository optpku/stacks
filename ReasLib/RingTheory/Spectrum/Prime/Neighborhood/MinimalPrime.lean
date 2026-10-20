/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Compact-open neighborhoods of minimal primes

@stack 00EV
-/

@[expose] public section

open TopologicalSpace

universe u

namespace PrimeSpectrum

variable {R : Type u} [CommRing R]

/-- Lemma 10.26.4: if a compact open subset of `Spec R` does not contain a
minimal prime `p`, then `p` has a basic-open neighborhood disjoint from it. -/
@[stacks 00EV]
theorem exists_basicOpen_disjoint_of_mem_minimalPrimes
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    (W : CompactOpens (PrimeSpectrum R)) (hpW : p ∉ W) :
    ∃ f : R, p ∈ basicOpen f ∧
      Disjoint (basicOpen f : Set (PrimeSpectrum R)) (W : Set (PrimeSpectrum R)) := sorry

end PrimeSpectrum
