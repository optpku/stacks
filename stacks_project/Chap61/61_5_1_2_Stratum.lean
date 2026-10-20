/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.VanishingStratum

@[expose] public section

universe u

/- Compatibility check for the reusable vanishing-pattern stratum definition. -/
#check (PrimeSpectrum.vanishingStratum :
  ∀ {A : Type u} [CommRing A], Set A → Set A → Set (PrimeSpectrum A))
