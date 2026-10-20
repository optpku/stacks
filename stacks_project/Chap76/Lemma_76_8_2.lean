module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.TopologicalInvariance

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.8.2: base change along an integral, universally injective, surjective
morphism of algebraic spaces restricts to equivalences of the small étale sites
and the affine étale sites. -/
@[stacks 07VW] #check
  (AlgebraicGeometry.AlgebraicSpace.smallEtalePullback.isEquivalence :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsIntegralHom f] [UniversallyInjective f] [Surjective f],
      (AlgebraicGeometry.AlgebraicSpace.smallEtalePullback f
        (AlgebraicGeometry.AlgebraicSpace.IsIntegralHom.relativelyRepresentable f)).IsEquivalence)

#check
  (AlgebraicGeometry.AlgebraicSpace.affineEtalePullback.isEquivalence :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsIntegralHom f] [UniversallyInjective f] [Surjective f],
      (AlgebraicGeometry.AlgebraicSpace.affineEtalePullback f
        (AlgebraicGeometry.AlgebraicSpace.IsIntegralHom.relativelyRepresentable f)).IsEquivalence)
