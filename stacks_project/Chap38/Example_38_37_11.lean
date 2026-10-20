/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.TwoGenerator.AlmostBlowup
import StacksCheckRecall

@[expose] public section

universe u

/- Example 38.37.11: for `f₁ f₂ : A`, the structure morphism from
`Proj (A[T₀, T₁] ⧸ (f₂ * T₀ - f₁ * T₁))` to `Spec A`, with center cut out by
`Ideal.span {f₁, f₂}`, determines an almost blowup square. -/
@[stacks 0EVH] #check
  (AlgebraicGeometry.TwoGeneratorProj.toSpec_isAlmostBlowupSquare :
    ∀ (A : CommRingCat.{u}) (f₁ f₂ : A),
      AlgebraicGeometry.IsAlmostBlowupSquare
        (AlgebraicGeometry.TwoGeneratorProj.toSpec A f₁ f₂)
        (AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec
          (AlgebraicGeometry.TwoGeneratorProj.centerIdeal A f₁ f₂)))
