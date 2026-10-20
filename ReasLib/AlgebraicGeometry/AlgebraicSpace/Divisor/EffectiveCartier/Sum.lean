module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Product
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.EffectiveCartier

/-!
# Sums of effective Cartier divisors on algebraic spaces

The sum of two effective Cartier divisors is the closed subspace cut out by
the product of their ideal sheaves.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The sum of two effective Cartier divisors on an algebraic space, as the
closed subspace cut out by the product of their ideal sheaves. -/
@[reducible] noncomputable def effectiveCartierDivisorSum {S : Scheme.{u}}
    {X : AlgebraicSpace S} (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι] :
    ClosedSubspace X where
  X := subscheme (IdealSubobject.mul D₁.idealSheaf D₂.idealSheaf)
  ι := subschemeι (IdealSubobject.mul D₁.idealSheaf D₂.idealSheaf)
  isClosedImmersion :=
    instIsClosedImmersion_subschemeι (IdealSubobject.mul D₁.idealSheaf D₂.idealSheaf)

/-- Given effective Cartier divisors on an algebraic space, their sum is the
closed subspace corresponding to the product of their quasi-coherent ideal
sheaves in `𝒪_X`. -/
theorem effectiveCartierDivisorSum_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι] :
    effectiveCartierDivisorSum D₁ D₂ =
      ClosedSubspace.ofQuasiCoherentIdeal
        (IdealSubobject.mul D₁.idealSheaf D₂.idealSheaf) :=
  rfl

/-- The ideal sheaf of a sum of effective Cartier divisors is the product of the
summands' ideal sheaves. -/
theorem effectiveCartierDivisorSum_idealSheaf {S : Scheme.{u}}
    {X : AlgebraicSpace S} (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι] :
    (effectiveCartierDivisorSum D₁ D₂).idealSheaf =
      IdealSubobject.mul D₁.idealSheaf D₂.idealSheaf :=
  ClosedSubspace.ofQuasiCoherentIdeal_idealSheaf
    (IdealSubobject.mul D₁.idealSheaf D₂.idealSheaf)

/-- The sum of two effective Cartier divisors is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_effectiveCartierDivisorSum {S : Scheme.{u}}
    {X : AlgebraicSpace S} (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι] :
    IsEffectiveCartierDivisor (effectiveCartierDivisorSum D₁ D₂).ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
