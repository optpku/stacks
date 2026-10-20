/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.SmoothCurve
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.Sum

/-!
# Ranks of sums on smooth relative curves

This file relates the canonical sum of finite locally free closed subschemes of a smooth
relative curve to the ranks of their structure morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The canonical sum of two finite locally free closed subschemes of ranks `d₁` and `d₂` on
a smooth relative curve is finite locally free of rank `d₁ + d₂`. -/
theorem isFiniteLocallyFreeOfRank_sum
    {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
    (D₁ D₂ : X.IdealSheafData) (d₁ d₂ : ℕ)
    (hD₁ : IsFiniteLocallyFreeOfRank (D₁.subschemeι ≫ f) d₁)
    (hD₂ : IsFiniteLocallyFreeOfRank (D₂.subschemeι ≫ f) d₂) :
    IsFiniteLocallyFreeOfRank
      ((effectiveCartierDivisorSum D₁ D₂).subschemeι ≫ f) (d₁ + d₂) := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
