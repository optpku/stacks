/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.AffineComparison
import StacksCheckRecall

open CategoryTheory

universe u

variable (S : AlgebraicGeometry.Scheme.{u})

/- Lemma 34.5.9 (1): the inclusion from affine schemes over `S` to schemes over `S` is special
cocontinuous for the standard affine and big smooth topologies. -/
@[stacks 06VC] #check
  (AlgebraicGeometry.Scheme.Smooth.AffineComparison.isSpecialCocontinuous S :
    (AlgebraicGeometry.Scheme.AffineOver.forget S).IsSpecialCocontinuous
      (AlgebraicGeometry.Scheme.Smooth.StandardAffine.topology S)
      (AlgebraicGeometry.Scheme.smoothOverTopology S))

/- Lemma 34.5.9 (2): the cocontinuous direct image from affine smooth sheaves to big smooth
sheaves is an equivalence. -/
@[stacks 06VC] #check
  (AlgebraicGeometry.Scheme.Smooth.AffineComparison.directImageIsEquivalence S :
    ((AlgebraicGeometry.Scheme.AffineOver.forget S).sheafPushforwardCocontinuous
      (Type (u + 1)) (AlgebraicGeometry.Scheme.Smooth.StandardAffine.topology S)
      (AlgebraicGeometry.Scheme.smoothOverTopology S)).IsEquivalence)
