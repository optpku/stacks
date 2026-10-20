/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum
import StacksCheckRecall

/-!
# Definition 31.13.6

The sum of effective Cartier divisors.

@stack 01WT
-/

@[expose] public section

/- Definition 31.13.6

The sum of two effective Cartier divisors is the ideal-sheaf datum cut out by the product of
their ideal sheaves.
-/
@[stacks 01WT] #check (AlgebraicGeometry.effectiveCartierDivisorSum_spec :
  ∀ {X : AlgebraicGeometry.Scheme} (D₁ D₂ : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D₁.subschemeι]
    [AlgebraicGeometry.IsEffectiveCartierDivisor D₂.subschemeι],
    AlgebraicGeometry.effectiveCartierDivisorSum D₁ D₂ = D₁ * D₂)

#check (AlgebraicGeometry.effectiveCartierDivisorSum :
  ∀ {X : AlgebraicGeometry.Scheme},
    X.IdealSheafData → X.IdealSheafData → X.IdealSheafData)

#check (AlgebraicGeometry.effectiveCartierDivisorSum_eq :
  ∀ {X : AlgebraicGeometry.Scheme} (D₁ D₂ : X.IdealSheafData),
    AlgebraicGeometry.effectiveCartierDivisorSum D₁ D₂ = D₁ * D₂)

#check (AlgebraicGeometry.ideal_effectiveCartierDivisorSum :
  ∀ {X : AlgebraicGeometry.Scheme} (D₁ D₂ : X.IdealSheafData),
    (AlgebraicGeometry.effectiveCartierDivisorSum D₁ D₂).ideal = D₁.ideal * D₂.ideal)
