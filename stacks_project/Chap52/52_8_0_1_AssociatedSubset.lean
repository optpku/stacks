/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.AssociatedSubset

@[expose] public section

universe u

#check (PrimeSpectrum.associatedSubset :
  {A : Type u} → [CommRing A] → Ideal A → Ideal A → Set (PrimeSpectrum A))
