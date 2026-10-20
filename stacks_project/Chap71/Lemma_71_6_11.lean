module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Pullback

/-!
# Lemma 71.6.11

The pullback of an effective Cartier divisor on an algebraic space is defined
when weakly associated points of the source map outside the divisor, or when
the morphism is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 71.6.11 (1): if every weakly associated point of `X'` maps outside
`D.pointsSet`, then the pullback of the effective Cartier divisor `D` along `f`
is defined. -/
@[stacks 083Z] #check
  (AlgebraicGeometry.AlgebraicSpace.pullbackDefined_of_weakAss_outside_support :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
      (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι]
      (hweak : ∀ x : Points X', x ∈ X'.weakAss → Points.map f x ∉ D.pointsSet),
      IsEffectiveCartierDivisor (D.inverseImageSubspace f).ι)

/- Lemma 71.6.11 (2): the pullback of an effective Cartier divisor along a flat
morphism of algebraic spaces is defined. -/
@[stacks 083Z] #check
  (AlgebraicGeometry.AlgebraicSpace.pullbackDefined_of_flat :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X) [Flat f]
      (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι],
      IsEffectiveCartierDivisor (D.inverseImageSubspace f).ι)
