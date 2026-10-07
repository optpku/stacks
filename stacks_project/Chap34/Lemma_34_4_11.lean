module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ChosenPresentation.AffineComparison
import StacksCheckRecall

open CategoryTheory

universe u v

/- Lemma 34.4.11: the inclusion of the chosen big affine étale site into the chosen big étale
slice is special cocontinuous. -/
@[stacks 021E] #check
  (AlgebraicGeometry.ChosenBigEtaleSite.AffineComparison.isSpecialCocontinuous :
    (X : AlgebraicGeometry.ChosenBigEtaleSite.{u, v}) → (S : X.carrier) →
      (AlgebraicGeometry.ChosenBigEtaleSite.bigAffineInclusion X S).IsSpecialCocontinuous
        (AlgebraicGeometry.ChosenBigEtaleSite.bigAffineTopology X S)
        (AlgebraicGeometry.ChosenBigEtaleSite.bigTopology X S))

/- The corresponding cocontinuous direct image is an equivalence on sheaves of types. -/
#check
  (AlgebraicGeometry.ChosenBigEtaleSite.AffineComparison.directImageIsEquivalence :
    (X : AlgebraicGeometry.ChosenBigEtaleSite.{u, v}) → (S : X.carrier) →
      ((AlgebraicGeometry.ChosenBigEtaleSite.bigAffineInclusion X S).sheafPushforwardCocontinuous
        (Type (max u v))
        (AlgebraicGeometry.ChosenBigEtaleSite.bigAffineTopology X S)
        (AlgebraicGeometry.ChosenBigEtaleSite.bigTopology X S)).IsEquivalence)
