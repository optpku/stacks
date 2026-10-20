module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.EffectiveCartier.EtaleLocal

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.6.2: a closed subspace of an algebraic space is an effective Cartier
 divisor exactly when it is so on some surjective étale scheme atlas, on every
 étale scheme chart, or has a principal nonzerodivisor presentation on a pointed
 affine étale chart at each point of its support. -/
@[stacks 083C] #check (AlgebraicGeometry.AlgebraicSpace.IsEffectiveCartierDivisor.tfae :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (D : ClosedSubspace X),
    List.TFAE
      [IsEffectiveCartierDivisor D.ι,
        IsEffectiveCartierDivisor.existsSurjectiveEtaleScheme D,
        IsEffectiveCartierDivisor.forallEtaleScheme D,
        IsEffectiveCartierDivisor.existsAffineEtaleNonZeroDivisor D])
