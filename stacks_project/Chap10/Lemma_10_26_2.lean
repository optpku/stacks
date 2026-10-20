/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.26.2

@stack 090M
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.26.2: for a commutative ring `R`, the prime spectrum `Spec R` is a spectral space in
the sense of Topology, Definition 5.23.1. In mathlib this is the canonical instance
`PrimeSpectrum.instSpectralSpace`. -/
@[stacks 090M]
#check @PrimeSpectrum.instSpectralSpace
