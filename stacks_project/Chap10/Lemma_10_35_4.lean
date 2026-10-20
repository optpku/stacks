/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.35.4

@stack 00G3
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.35.4: a commutative ring `R` is Jacobson if and only if its prime spectrum
`PrimeSpectrum R` is a Jacobson topological space. This is exactly the canonical mathlib theorem
`PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace`. -/
@[stacks 00G3]
#check @PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace
