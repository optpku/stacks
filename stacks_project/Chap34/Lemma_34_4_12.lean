/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ChosenPresentation.SmallAffineComparison
import StacksCheckRecall

universe u v

/- Lemma 34.4.12: the inclusion of the chosen small affine étale site into the
chosen small étale site is special cocontinuous. -/
@[stacks 04HR] #check
  (AlgebraicGeometry.ChosenBigEtaleSite.SmallAffineComparison.isSpecialCocontinuous :
    ∀ (X : AlgebraicGeometry.ChosenBigEtaleSite.{u, v}) (S : X.carrier),
      CategoryTheory.Functor.IsSpecialCocontinuous
        (AlgebraicGeometry.ChosenBigEtaleSite.smallAffineInclusion X S)
        (AlgebraicGeometry.ChosenBigEtaleSite.smallAffineTopology X S)
        (AlgebraicGeometry.ChosenBigEtaleSite.smallTopology X S))

/- Its cocontinuous direct image induces an equivalence from sheaves on the
chosen small affine étale site to sheaves on the chosen small étale site. -/
#check
  (AlgebraicGeometry.ChosenBigEtaleSite.SmallAffineComparison.directImageIsEquivalence :
    ∀ (X : AlgebraicGeometry.ChosenBigEtaleSite.{u, v}) (S : X.carrier),
      CategoryTheory.Functor.IsEquivalence
        ((AlgebraicGeometry.ChosenBigEtaleSite.smallAffineInclusion X S).sheafPushforwardCocontinuous
            (Type (max u v))
            (AlgebraicGeometry.ChosenBigEtaleSite.smallAffineTopology X S)
            (AlgebraicGeometry.ChosenBigEtaleSite.smallTopology X S)))
