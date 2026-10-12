/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Lemma_61_12_11_AffineComparison
import StacksCheckRecall

open CategoryTheory

universe u v

/- Lemma 61.12.11 (1): the inclusion of the chosen big affine pro-étale site into the chosen big
pro-étale slice is special cocontinuous. -/
@[stacks 098N] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.AffineComparison.isSpecialCocontinuous :
    (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v}) → (S : X.carrier) →
      (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineInclusion X S).IsSpecialCocontinuous
        (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineTopology X S)
        (AlgebraicGeometry.ChosenBigProetaleSite.bigTopology X S))

/- Lemma 61.12.11 (2): the corresponding cocontinuous direct image is an equivalence on sheaves of
types. -/
@[stacks 098N] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.AffineComparison.directImageIsEquivalence :
    (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v}) → (S : X.carrier) →
      ((AlgebraicGeometry.ChosenBigProetaleSite.bigAffineInclusion X S).sheafPushforwardCocontinuous
        (Type (max u v))
        (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineTopology X S)
        (AlgebraicGeometry.ChosenBigProetaleSite.bigTopology X S)).IsEquivalence)
