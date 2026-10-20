/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.Constructible
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.29.2 (Tag 00F7): maps of prime spectra preserve the constructible topology.

@stack 00F7
-/

-- Declarations for this item will be appended below by the statement pipeline.

-- Lemma 10.29.2 (1): a ring homomorphism induces a spectral map on prime spectra.
@[stacks 00F7 "(1)"]
#check @PrimeSpectrum.isSpectralMap_comap

-- Lemma 10.29.2 (2): its inverse image preserves constructible subsets.
@[stacks 00F7 "(2)"]
#check @PrimeSpectrum.isConstructible_preimage_comap
