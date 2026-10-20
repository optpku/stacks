/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.MeromorphicFunction.ComplexLineWithSquareZeroFibers
import StacksCheckRecall

open scoped nonZeroDivisors

/- Example 31.23.2: Let
`A = ℂ[x, {y α}_{α : ℂ}] / ((x - α) * y α, y α * y β)`.
Every element of `A` has a unique expression `f(x) + ∑ α, λ α * y α`, where the coefficient
family `λ : ℂ →₀ ℂ` is finitely supported. For `X = Spec A`, every non-zero-divisor in each
principal localization `A_f` is a unit, so the canonical map `𝒪_X ⟶ 𝒦_X` is an isomorphism. -/
@[stacks 01X3] #check
  (AlgebraicGeometry.ComplexLineWithSquareZeroFibers.toMeromorphicFunctionSheafHom_isIso :
    CategoryTheory.IsIso
      (AlgebraicGeometry.LocallyRingedSpace.toMeromorphicFunctionSheafHom
        AlgebraicGeometry.ComplexLineWithSquareZeroFibers.spectrum.toLocallyRingedSpace))

/- The normal-form map records existence and uniqueness of the polynomial-plus-fiber
expression. -/
#check
  (AlgebraicGeometry.ComplexLineWithSquareZeroFibers.normalForm_bijective :
    Function.Bijective AlgebraicGeometry.ComplexLineWithSquareZeroFibers.normalForm)

/- Every non-zero-divisor in every principal localization of the coordinate ring is a unit. -/
#check
  (AlgebraicGeometry.ComplexLineWithSquareZeroFibers.isUnit_of_mem_nonZeroDivisors_localizationAway :
    ∀ (f : AlgebraicGeometry.ComplexLineWithSquareZeroFibers.CoordinateRing)
      (z : Localization.Away f),
      z ∈ nonZeroDivisors (Localization.Away f) → IsUnit z)
