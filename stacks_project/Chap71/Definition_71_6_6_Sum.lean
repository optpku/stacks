module

public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import stacks_project.Chap71.Definition_71_6_1_EffectiveCartier
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Product
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Sum

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

#check
  (AlgebraicGeometry.AlgebraicSpace.IdealSubobject.mul :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} →
      IdealSubobject X → IdealSubobject X → IdealSubobject X)

#check
  (AlgebraicGeometry.AlgebraicSpace.IdealSubobject.mul_eq :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (I J : IdealSubobject X),
      IdealSubobject.mul I J = Modules.idealPowerSmulSubobject I J 1)

#check
  (AlgebraicGeometry.AlgebraicSpace.IdealSubobject.mul_spec :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (I J : IdealSubobject X),
      IdealSubobject.mul I J =
        imageSubobject (Modules.action I J.toModule ≫ J.arrow))

#check
  (AlgebraicGeometry.AlgebraicSpace.IsQuasiCoherent.mul :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (I J : IdealSubobject X)
      [IsQuasiCoherent I] [IsQuasiCoherent J],
      IsQuasiCoherent (IdealSubobject.mul I J))

#check
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
  (AlgebraicGeometry.AlgebraicSpace.effectiveCartierDivisorSum_idealSheaf :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (D₁ D₂ : ClosedSubspace X)
      [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι],
      (effectiveCartierDivisorSum D₁ D₂).idealSheaf =
        IdealSubobject.mul D₁.idealSheaf D₂.idealSheaf)
