/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.Separation
public import ReasLib.Topology.Indiscrete
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.6.7: show that the spectrum of a ring need not be Hausdorff,
prove that the spectrum of every commutative ring is T₀, and give an example
of a topological space that is not T₀. The spectrum of ℤ is a counterexample
to Hausdorffness, and the indiscrete two-point space is a counterexample to
the T₀ property. -/
@[stacks 02D2]
#check (PrimeSpectrum.notT2SpaceInt : ¬ T2Space (PrimeSpectrum ℤ))

/- Canonical T₀ instance for the prime spectrum of every commutative ring. -/
#check (PrimeSpectrum.instT0Space : ∀ {R : Type u} [CommSemiring R], T0Space (PrimeSpectrum R))

/- Concrete non-T₀ example given by the indiscrete topology on `Bool`. -/
#check (IndiscreteTopology.not_t0Space_withTopology_bool : ¬ T0Space (WithTopology Bool ⊤))
