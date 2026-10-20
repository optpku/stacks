/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap71.Definition_71_6_6_Sum
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Sum.Effective

/-!
# Effectivity of sums of effective Cartier divisors

The product of two invertible quasi-coherent ideal sheaves remains invertible,
so the corresponding sum of effective Cartier divisors is again effective
Cartier.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.isEffectiveCartierDivisor_mul :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (I J : IdealSubobject X)
      [IsQuasiCoherent I] [IsQuasiCoherent J]
      [IsEffectiveCartierDivisor (ClosedSubspace.ofQuasiCoherentIdeal I).ι]
      [IsEffectiveCartierDivisor (ClosedSubspace.ofQuasiCoherentIdeal J).ι],
      IsEffectiveCartierDivisor
        (ClosedSubspace.ofQuasiCoherentIdeal (IdealSubobject.mul I J)).ι)

#check
  (AlgebraicGeometry.AlgebraicSpace.instIsEffectiveCartierDivisor_idealProduct :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (I J : IdealSubobject X)
      [IsQuasiCoherent I] [IsQuasiCoherent J]
      [CategoryTheory.MonoidalCategory.isInvertibleObject I.toModule]
      [CategoryTheory.MonoidalCategory.isInvertibleObject J.toModule],
      IsEffectiveCartierDivisor (subschemeι (IdealSubobject.mul I J)))

#check
  (AlgebraicGeometry.AlgebraicSpace.isEffectiveCartierDivisor_sum :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (D₁ D₂ : ClosedSubspace X)
      [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι],
      IsEffectiveCartierDivisor (effectiveCartierDivisorSum D₁ D₂).ι)
