module

public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import stacks_project.Chap71.Definition_71_6_1_EffectiveCartier

/-!
# Sums of effective Cartier divisors on algebraic spaces

The product of two ideal subobjects of `𝒪_X` is the image of the ideal-sheaf
action. The sum of two effective Cartier divisors is the closed subspace cut
out by that product.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IdealSubobject

/-- The product of two ideal subobjects of `𝒪_X`, obtained by the first
ideal-power action on the second. -/
noncomputable def mul {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I J : IdealSubobject X) : IdealSubobject X :=
  Modules.idealPowerSmulSubobject I J 1

/-- The product of ideal subobjects is the first ideal-power action on the
second. -/
theorem mul_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (I J : IdealSubobject X) :
    mul I J = Modules.idealPowerSmulSubobject I J 1 :=
  sorry

/-- The product of ideal subobjects is the image of the action `I ⊗ J ⟶ 𝒪_X`. -/
theorem mul_spec {S : Scheme.{u}} {X : AlgebraicSpace S} (I J : IdealSubobject X) :
    mul I J = imageSubobject (Modules.action I J.toModule ≫ J.arrow) :=
  sorry

end IdealSubobject

namespace IsQuasiCoherent

/-- The product of quasi-coherent ideal sheaves is quasi-coherent. -/
instance mul {S : Scheme.{u}} {X : AlgebraicSpace S} (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    IsQuasiCoherent (IdealSubobject.mul I J) :=
  sorry

end IsQuasiCoherent

/-- The sum of two effective Cartier divisors on an algebraic space, as the
closed subspace cut out by the product of their ideal sheaves. -/
noncomputable def effectiveCartierDivisorSum {S : Scheme.{u}}
    {X : AlgebraicSpace S} (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι] :
    ClosedSubspace X :=
  ClosedSubspace.ofQuasiCoherentIdeal (IdealSubobject.mul D₁.idealSheaf D₂.idealSheaf)

/-- The sum of two effective Cartier divisors is the closed subspace of the
product of their ideal sheaves. -/
theorem effectiveCartierDivisorSum_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι] :
    effectiveCartierDivisorSum D₁ D₂ =
      ClosedSubspace.ofQuasiCoherentIdeal
        (IdealSubobject.mul D₁.idealSheaf D₂.idealSheaf) :=
  sorry

/-- Given effective Cartier divisors on an algebraic space, their sum is the
closed subspace corresponding to the product of their quasi-coherent ideal
sheaves in `𝒪_X`. -/
theorem effectiveCartierDivisorSum_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι] :
    effectiveCartierDivisorSum D₁ D₂ =
      ClosedSubspace.ofQuasiCoherentIdeal
        (IdealSubobject.mul D₁.idealSheaf D₂.idealSheaf) :=
  sorry

/-- The ideal sheaf of a sum of effective Cartier divisors is the product of the
summands' ideal sheaves. -/
theorem effectiveCartierDivisorSum_idealSheaf {S : Scheme.{u}}
    {X : AlgebraicSpace S} (D₁ D₂ : ClosedSubspace X)
    [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι] :
    (effectiveCartierDivisorSum D₁ D₂).idealSheaf =
      IdealSubobject.mul D₁.idealSheaf D₂.idealSheaf :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
