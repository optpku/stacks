/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.Complex
import StacksCheckRecall

/-!
# Example 29.9.5

Bijectivity on points is not preserved by base change.
-/

@[expose] public section

open scoped TensorProduct

/- Example 29.9.5 (1): The map on prime spectra induced by ℝ → ℂ is bijective. -/
@[stacks 0496] #check
  (complexSpecToRealSpec_bijective :
    Function.Bijective (PrimeSpectrum.comap (algebraMap ℝ ℂ)))

/- Example 29.9.5 (2): After base change to ℂ, the induced map is not injective. -/
@[stacks 0496] #check
  (complexTensorSquareSpecToComplexSpec_not_injective :
    ¬ Function.Injective (PrimeSpectrum.comap (algebraMap ℂ (ℂ ⊗[ℝ] ℂ))))
