/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import StacksCheckRecall

@[expose] public section

/-!
# Theorem 10.29.10 (Chevalley's Theorem)

@stack 00FE
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 10.29.10 (Chevalley's Theorem): suppose that `R →+* S` is of finite presentation. Then
the image of a constructible subset of `Spec(S)` in `Spec(R)` is constructible. This is exactly the
canonical theorem `PrimeSpectrum.isConstructible_comap_image`. -/
@[stacks 00FE]
#check @PrimeSpectrum.isConstructible_comap_image
