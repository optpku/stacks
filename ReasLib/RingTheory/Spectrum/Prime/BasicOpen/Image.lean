/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Images of Principal Basic Opens

@stack 00FB
-/

@[expose] public section

universe u v

namespace PrimeSpectrum

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]

/-- The image of a principal basic open under a map of prime spectra is compact. -/
@[stacks 00FB "compact image of a principal basic open"]
theorem isCompact_image_comap_basicOpen (f : R →+* S) (s : S) :
    IsCompact (comap f '' (basicOpen s : Set (PrimeSpectrum S))) :=
  (isCompact_basicOpen s).image (continuous_comap f)

end PrimeSpectrum
