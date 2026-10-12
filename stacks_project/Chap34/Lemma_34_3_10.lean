/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.AffineComparison
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 34.3.10: the inclusion from affine schemes over `S` with the standard Zariski
topology to schemes over `S` with the big Zariski topology is special cocontinuous. -/
@[stacks 020W] #check
  (AlgebraicGeometry.Scheme.Zariski.AffineComparison.isSpecialCocontinuous :
    ∀ (S : AlgebraicGeometry.Scheme.{u}),
      (AlgebraicGeometry.Scheme.bigAffineZariskiInclusion S).IsSpecialCocontinuous
        (AlgebraicGeometry.Scheme.bigAffineZariskiTopology S)
        (AlgebraicGeometry.Scheme.bigZariskiTopology S))

/- Its cocontinuous direct image from affine-site sheaves to big-site sheaves is an
equivalence. -/
#check
  (AlgebraicGeometry.Scheme.Zariski.AffineComparison.directImageIsEquivalence :
    ∀ (S : AlgebraicGeometry.Scheme.{u}),
      ((AlgebraicGeometry.Scheme.bigAffineZariskiInclusion S).sheafPushforwardCocontinuous
        (Type (u + 1)) (AlgebraicGeometry.Scheme.bigAffineZariskiTopology S)
        (AlgebraicGeometry.Scheme.bigZariskiTopology S)).IsEquivalence)
