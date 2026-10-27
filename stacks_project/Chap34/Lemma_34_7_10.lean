/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.ChosenPresentation.Limits
import StacksCheckRecall

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

variable (X : SchAlphaBigSite.{u, v} Scheme.fppfPrecoverage) (S : X.carrier)

/- Lemma 34.7.10 (1): the chosen big fppf carrier has fibre products. -/
@[stacks 021U] #check (AlgebraicGeometry.SchAlphaBigSite.carrierHasPullbacks X :
  CategoryTheory.Limits.HasPullbacks X.carrier)

/- Lemma 34.7.10 (2): the functor from the chosen big fppf carrier to schemes
commutes with fibre products. -/
@[stacks 021U] #check (AlgebraicGeometry.SchAlphaBigSite.toSchemePreservesPullbacks X :
  CategoryTheory.Limits.PreservesLimitsOfShape CategoryTheory.Limits.WalkingCospan X.toScheme)

/- Lemma 34.7.10 (3): the chosen big fppf slice over `S` has fibre products. -/
@[stacks 021U] #check (AlgebraicGeometry.ChosenBigSite.sliceHasPullbacks X.toChosenBigSite S :
  CategoryTheory.Limits.HasPullbacks
    (AlgebraicGeometry.ChosenBigFppfSite.bigSite X.toChosenBigSite S))

/- Lemma 34.7.10 (4): the functor from the chosen big fppf slice over `S` to
schemes commutes with fibre products. -/
@[stacks 021U] #check (AlgebraicGeometry.ChosenBigSite.sliceToSchemePreservesPullbacks X.toChosenBigSite S :
  CategoryTheory.Limits.PreservesLimitsOfShape CategoryTheory.Limits.WalkingCospan
    (AlgebraicGeometry.ChosenBigFppfSite.bigToScheme X.toChosenBigSite S))

/- Lemma 34.7.10 (5): the chosen big affine fppf carrier over `S` has fibre
products. -/
@[stacks 021U] #check
  (AlgebraicGeometry.ChosenBigFppfSite.bigAffineSiteHasPullbacks X.toChosenBigSite S :
    CategoryTheory.Limits.HasPullbacks
      (AlgebraicGeometry.ChosenBigFppfSite.bigAffineSite X.toChosenBigSite S))

/- Lemma 34.7.10 (6): the functor from the chosen big affine fppf carrier over
`S` to schemes commutes with fibre products. -/
@[stacks 021U] #check
  (AlgebraicGeometry.ChosenBigFppfSite.bigAffineToSchemePreservesPullbacks X.toChosenBigSite S :
    CategoryTheory.Limits.PreservesLimitsOfShape CategoryTheory.Limits.WalkingCospan
      (AlgebraicGeometry.ChosenBigFppfSite.bigAffineToScheme X.toChosenBigSite S))

/- Lemma 34.7.10 (7): the identity object `S/S` is terminal in the chosen big
fppf slice over `S`. -/
@[stacks 021U] #check (AlgebraicGeometry.ChosenBigFppfSite.bigSiteIdentityTerminal X.toChosenBigSite S :
  CategoryTheory.Limits.IsTerminal
    (CategoryTheory.Over.mk (𝟙 S) : AlgebraicGeometry.ChosenBigFppfSite.bigSite X.toChosenBigSite S))

end AlgebraicGeometry.ChosenBigFppfSite
