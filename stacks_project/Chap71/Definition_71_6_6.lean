/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Sum
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Definition 71.6.6
Let `S` be a scheme and let `X` be an algebraic space over `S`. Given effective
Cartier divisors `D₁`, `D₂` on `X`, the sum `D = D₁ + D₂` is the closed subspace
of `X` corresponding to the quasi-coherent sheaf of ideals
`IdealSubobject.mul D₁.idealSheaf D₂.idealSheaf ⊂ 𝒪_X`.
-/
@[stacks 083U] #check
  (AlgebraicGeometry.AlgebraicSpace.effectiveCartierDivisorSum :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (D₁ D₂ : ClosedSubspace X)
      [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι],
      ClosedSubspace X)

#check
  (AlgebraicGeometry.AlgebraicSpace.effectiveCartierDivisorSum_spec :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (D₁ D₂ : ClosedSubspace X)
      [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι],
      effectiveCartierDivisorSum D₁ D₂ =
        ClosedSubspace.ofQuasiCoherentIdeal
          (IdealSubobject.mul D₁.idealSheaf D₂.idealSheaf))

#check
  (AlgebraicGeometry.AlgebraicSpace.IdealSubobject.mul :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} →
      IdealSubobject X → IdealSubobject X → IdealSubobject X)

#check
  (AlgebraicGeometry.AlgebraicSpace.effectiveCartierDivisorSum_idealSheaf :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (D₁ D₂ : ClosedSubspace X)
      [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι],
      (effectiveCartierDivisorSum D₁ D₂).idealSheaf =
        IdealSubobject.mul D₁.idealSheaf D₂.idealSheaf)
