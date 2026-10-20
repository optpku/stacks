module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Pullback
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 71.6.10
Let `S` be a scheme. Let `f : X' ⟶ X` be a morphism of algebraic spaces over `S`.
Let `D ⊂ X` be an effective Cartier divisor. The pullback of `D` by `f` is defined
when the inverse-image closed subspace `D.inverseImageSubspace f ⊂ X'` is an effective
Cartier divisor. In that case the pullback is that inverse image, written `f^*D`
or `f⁻¹(D)`. -/
@[stacks 083Y] #check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.IsPullbackDefined :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (D : ClosedSubspace X),
      [IsEffectiveCartierDivisor D.ι] → (Y ⟶ X) → Prop)

#check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.isPullbackDefined_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (D : ClosedSubspace X),
      [IsEffectiveCartierDivisor D.ι] → ∀ (f : Y ⟶ X),
        D.IsPullbackDefined f ↔
          IsEffectiveCartierDivisor (D.inverseImageSubspace f).ι)
