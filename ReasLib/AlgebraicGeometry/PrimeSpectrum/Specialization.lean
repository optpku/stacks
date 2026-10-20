/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Sober
public import ReasLib.RingTheory.Spectrum.Prime.ClosedPoint

@[expose] public section

universe u

namespace PrimeSpectrum

variable (R : Type u) [CommSemiring R]

/-- A prime-spectrum point generalizes another point exactly when its ideal is contained
in the other point's ideal. -/
theorem generalization_iff_subset (p q : PrimeSpectrum R) :
    p ⤳ q ↔ p.asIdeal ≤ q.asIdeal := sorry

/-- A prime-spectrum point is closed exactly when it has no proper specialization. -/
theorem mem_closedPoints_iff_no_proper_specialization (p : PrimeSpectrum R) :
    p ∈ closedPoints (PrimeSpectrum R) ↔ ∀ q : PrimeSpectrum R, p ⤳ q → q = p := sorry

/-- A prime-spectrum point is generic for an irreducible component exactly when its ideal
is a minimal prime. -/
theorem mem_genericPoints_iff_mem_minimalPrimes (p : PrimeSpectrum R) :
    p ∈ genericPoints (PrimeSpectrum R) ↔ p.asIdeal ∈ minimalPrimes R := sorry

/-- A prime-spectrum point is generic for an irreducible component exactly when it has
no proper generalization. -/
theorem mem_genericPoints_iff_no_proper_generalization (p : PrimeSpectrum R) :
    p ∈ genericPoints (PrimeSpectrum R) ↔ ∀ q : PrimeSpectrum R, q ⤳ p → q = p := sorry

end PrimeSpectrum
