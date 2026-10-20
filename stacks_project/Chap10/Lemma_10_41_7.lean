/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.41.7

@stack 00I0
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.41.7 (00I0) (1): if a constructible subset of `Spec(R)` is stable under
specialization, then it is closed. This is exactly the canonical prime-spectrum theorem
`PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible`. -/
@[stacks 00I0 "constructible specialization-closed sets"]
#check @PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible

/- Lemma 10.41.7 (00I0) (2): if a constructible subset of `Spec(R)` is stable under
generalization, then it is open. This is exactly the canonical prime-spectrum theorem
`PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible`. -/
@[stacks 00I0 "constructible generalization-open sets"]
#check @PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible
