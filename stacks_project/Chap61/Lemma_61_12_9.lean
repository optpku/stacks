/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Lemma_61_12_9_Site
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 61.12.9 (1): the small pro-étale site of a scheme in a chosen big
pro-étale site is a site. -/
@[stacks 098L] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallPrecoverage.instIsSite :
    ∀ (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v})
      (S : X.carrier),
      CategoryTheory.Precoverage.IsSite
        (AlgebraicGeometry.ChosenBigProetaleSite.smallPrecoverage X S))

/- Lemma 61.12.9 (2): the big affine pro-étale site of a scheme in a chosen big
pro-étale site is a site. -/
@[stacks 098L] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineStandardPrecoverage.instIsSite :
    ∀ (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v})
      (S : X.carrier),
      CategoryTheory.Precoverage.IsSite
        (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineStandardPrecoverage X S))
