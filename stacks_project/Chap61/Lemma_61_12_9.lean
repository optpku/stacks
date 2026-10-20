/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.SiteAxioms
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 61.12.9 (1): the small pro-étale site of a scheme in a chosen big
pro-étale site is a site. -/
@[stacks 098L] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallPrecoverage.isSite :
    ∀ (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v})
      (S : X.carrier),
      CategoryTheory.Precoverage.IsSite
        (AlgebraicGeometry.ChosenBigProetaleSite.smallPrecoverage X S))

/- Lemma 61.12.9 (2): the big affine pro-étale site of a scheme in a chosen big
pro-étale site is a site. -/
@[stacks 098L] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineStandardPrecoverage.isSite :
    ∀ (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v})
      (S : X.carrier),
      CategoryTheory.Precoverage.IsSite
        (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineStandardPrecoverage X S))
