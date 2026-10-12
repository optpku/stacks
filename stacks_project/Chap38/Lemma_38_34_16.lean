/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.ChosenPresentation.AffineComparison
import StacksCheckRecall

open CategoryTheory

universe u v

variable (X : AlgebraicGeometry.ChosenBigHSite.{u, v}) (S : X.carrier)

/- Lemma 38.34.16 (1): the inclusion from the affine objects over `S` to the
chosen big h slice over `S` is cocontinuous. -/
@[stacks 0EU4] #check
  (AlgebraicGeometry.ChosenBigHSite.AffineComparison.isCocontinuous X S :
    (AlgebraicGeometry.ChosenBigSite.affineInclusion X S).IsCocontinuous
      (AlgebraicGeometry.ChosenBigHSite.bigAffineTopology X S)
      (AlgebraicGeometry.ChosenBigHSite.bigTopology X S))

/- Lemma 38.34.16 (2): the cocontinuous direct image from affine h sheaves to
big h sheaves is an equivalence. -/
@[stacks 0EU4] #check
  (AlgebraicGeometry.ChosenBigHSite.AffineComparison.directImageIsEquivalence X S :
    (@CategoryTheory.Functor.sheafPushforwardCocontinuous _ _ _ _
      (AlgebraicGeometry.ChosenBigSite.affineInclusion X S) (Type (max u v)) _
      (AlgebraicGeometry.ChosenBigHSite.bigAffineTopology X S)
      (AlgebraicGeometry.ChosenBigHSite.bigTopology X S)
      (AlgebraicGeometry.ChosenBigHSite.AffineComparison.isCocontinuous X S)
      inferInstance).IsEquivalence)
