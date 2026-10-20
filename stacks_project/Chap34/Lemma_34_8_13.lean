/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.ChosenPresentation.Limits
import StacksCheckRecall

open CategoryTheory

universe u v

variable (X : AlgebraicGeometry.ChosenBigPhSite.{u, v})
  (S : X.carrier)

/- Lemma 34.8.13 (1): the carrier of the chosen big ph site has fibre products. -/
@[stacks 0DBN] #check
  (AlgebraicGeometry.ChosenBigSite.carrierHasPullbacks X :
    CategoryTheory.Limits.HasPullbacks X.carrier)

/- Lemma 34.8.13 (2): the functor from the chosen big ph carrier to schemes commutes
with fibre products. -/
@[stacks 0DBN] #check
  (AlgebraicGeometry.ChosenBigSite.toSchemePreservesPullbacks X :
    CategoryTheory.Limits.PreservesLimitsOfShape
      CategoryTheory.Limits.WalkingCospan X.toScheme)

/- Lemma 34.8.13 (3): the chosen big ph site over `S` has fibre products. -/
@[stacks 0DBN] #check
  (AlgebraicGeometry.ChosenBigSite.sliceHasPullbacks X S :
    CategoryTheory.Limits.HasPullbacks
      (AlgebraicGeometry.ChosenBigPhSite.bigSite X S))

/- Lemma 34.8.13 (4): the source-scheme functor from the chosen big ph site over `S`
commutes with fibre products. -/
@[stacks 0DBN] #check
  (AlgebraicGeometry.ChosenBigSite.sliceToSchemePreservesPullbacks X S :
    CategoryTheory.Limits.PreservesLimitsOfShape
      CategoryTheory.Limits.WalkingCospan
        (AlgebraicGeometry.ChosenBigPhSite.bigToScheme X S))

/- Lemma 34.8.13 (5): the chosen big affine ph site over `S` has fibre products. -/
@[stacks 0DBN] #check
  (AlgebraicGeometry.ChosenBigPhSite.bigAffineSiteHasPullbacks X S :
    CategoryTheory.Limits.HasPullbacks
      (AlgebraicGeometry.ChosenBigPhSite.bigAffineSite X S))

/- Lemma 34.8.13 (6): the source-scheme functor from the chosen big affine ph site over
`S` commutes with fibre products. -/
@[stacks 0DBN] #check
  (AlgebraicGeometry.ChosenBigPhSite.bigAffineToSchemePreservesPullbacks X S :
    CategoryTheory.Limits.PreservesLimitsOfShape
      CategoryTheory.Limits.WalkingCospan
        (AlgebraicGeometry.ChosenBigPhSite.bigAffineToScheme X S))

/- Lemma 34.8.13 (7): the identity object `S/S` is final in the chosen big ph site. -/
@[stacks 0DBN] #check
  (AlgebraicGeometry.ChosenBigPhSite.bigSiteIdentityTerminal X S :
    CategoryTheory.Limits.IsTerminal
      (CategoryTheory.Over.mk (𝟙 S) :
        AlgebraicGeometry.ChosenBigPhSite.bigSite X S))
