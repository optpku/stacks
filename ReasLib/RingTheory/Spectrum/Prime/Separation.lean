/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

namespace PrimeSpectrum

/-- The prime spectrum of the integers is not Hausdorff. -/
theorem notT2SpaceInt : ¬ T2Space (PrimeSpectrum ℤ) := sorry

end PrimeSpectrum
