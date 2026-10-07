module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.AffineComparison
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 34.7.11 (1): the inclusion from affine schemes over `S` to schemes over `S` is
cocontinuous for the affine and big fppf topologies. -/
@[stacks 021V] #check
  (AlgebraicGeometry.Scheme.Fppf.AffineComparison.isCocontinuous :
    ∀ (S : AlgebraicGeometry.Scheme.{u}),
      (AlgebraicGeometry.Scheme.AffineOver.forget S).IsCocontinuous
        (AlgebraicGeometry.Scheme.bigAffineFppfTopology S)
        (AlgebraicGeometry.Scheme.fppfTopology.over S))

/- Lemma 34.7.11 (2): the cocontinuous direct image from affine fppf sheaves to big fppf
sheaves is an equivalence. -/
@[stacks 021V] #check
  (AlgebraicGeometry.Scheme.Fppf.AffineComparison.directImageIsEquivalence :
    ∀ (S : AlgebraicGeometry.Scheme.{u}),
      ((AlgebraicGeometry.Scheme.AffineOver.forget S).sheafPushforwardCocontinuous
        (Type (u + 1)) (AlgebraicGeometry.Scheme.bigAffineFppfTopology S)
        (AlgebraicGeometry.Scheme.fppfTopology.over S)).IsEquivalence)
