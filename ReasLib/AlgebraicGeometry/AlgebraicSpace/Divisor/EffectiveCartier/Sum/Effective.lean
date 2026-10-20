module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Sum

/-!
# Effectivity of sums of effective Cartier divisors

The product of two invertible quasi-coherent ideal sheaves remains invertible,
so the corresponding sum of effective Cartier divisors is again effective
Cartier.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The product of two quasi-coherent ideal sheaves of effective Cartier
 divisors again cuts out an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_mul {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I J : IdealSubobject X) [IsQuasiCoherent I] [IsQuasiCoherent J]
    [IsEffectiveCartierDivisor (ClosedSubspace.ofQuasiCoherentIdeal I).ι]
    [IsEffectiveCartierDivisor (ClosedSubspace.ofQuasiCoherentIdeal J).ι] :
    IsEffectiveCartierDivisor
      (ClosedSubspace.ofQuasiCoherentIdeal (IdealSubobject.mul I J)).ι :=
  sorry

/-- The product of two quasi-coherent ideal sheaves with invertible underlying
modules cuts out an effective Cartier divisor. -/
instance instIsEffectiveCartierDivisor_idealProduct {S : Scheme.{u}}
    {X : AlgebraicSpace S} (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J]
    [isInvertibleObject I.toModule] [isInvertibleObject J.toModule] :
    IsEffectiveCartierDivisor (subschemeι (IdealSubobject.mul I J)) :=
  sorry

/-- The sum of two effective Cartier divisors on an algebraic space is again an
 effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_sum {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι] :
    IsEffectiveCartierDivisor (effectiveCartierDivisorSum D₁ D₂).ι := by
  infer_instance

end AlgebraicGeometry.AlgebraicSpace
