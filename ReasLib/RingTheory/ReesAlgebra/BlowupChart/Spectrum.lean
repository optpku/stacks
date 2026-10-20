/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart

/-!
# Spectra of affine blowup charts

This leaf records the spectral consequence of the canonical comparison from
an affine blowup chart to the principal localization of its base ring. It is
kept separate from the construction so applications can import the density
criterion without the chapter-facing presentation of the result.
-/

@[expose] public section

universe u

open PrimeSpectrum

namespace AffineBlowupChart

variable {R : Type u} [CommRing R]

/-- Lemma 10.70.11 (052T): if the distinguished chart parameter avoids every minimal prime of
the base ring, then the induced map on prime spectra has dense range. -/
@[stacks 052T "dense spectrum map of an affine blowup chart"]
theorem denseRange_comap_of_not_mem_minimalPrimes
    (I : Ideal R) (a : I)
    (h_minimal : ∀ p ∈ minimalPrimes R, a.1 ∉ p) :
    DenseRange (comap (algebraMap R (affineBlowupChart I a))) := sorry

end AffineBlowupChart
