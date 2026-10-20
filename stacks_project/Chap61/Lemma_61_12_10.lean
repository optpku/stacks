/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.FiniteLimits
import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Affine
import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.Limits
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

variable (X : AlgebraicGeometry.ChosenBigSite.WithSpecZ.{u, v}
    Scheme.proetalePrecoverage) (S : X.toChosenBigSite.carrier)

/- Lemma 61.12.10 (1): the carrier of the chosen big pro-étale site has fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.carrierHasPullbacks X.toChosenBigSite :
    HasPullbacks X.toChosenBigSite.carrier)

/- Lemma 61.12.10 (2): the functor from the chosen big pro-étale carrier to schemes
commutes with fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.toSchemePreservesPullbacks X.toChosenBigSite :
    PreservesLimitsOfShape WalkingCospan X.toChosenBigSite.toScheme)

/- Lemma 61.12.10 (3): the chosen big pro-étale site of `S` has fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.sliceHasPullbacks X.toChosenBigSite S :
    HasPullbacks (AlgebraicGeometry.ChosenBigProetaleSite.bigSite X.toChosenBigSite S))

/- Lemma 61.12.10 (4): the functor from the chosen big pro-étale site of `S` to schemes
commutes with fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.sliceToSchemePreservesPullbacks X.toChosenBigSite S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigProetaleSite.bigToScheme X.toChosenBigSite S))

/- Lemma 61.12.10 (5): the chosen small pro-étale site of `S` has fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallSiteHasPullbacks X.toChosenBigSite S :
    HasPullbacks (AlgebraicGeometry.ChosenBigProetaleSite.smallSite X.toChosenBigSite S))

/- Lemma 61.12.10 (6): the functor from the chosen small pro-étale site of `S` to schemes
commutes with fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallToSchemePreservesPullbacks X.toChosenBigSite S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigProetaleSite.smallToScheme X.toChosenBigSite S))

/- Lemma 61.12.10 (7): the chosen big affine pro-étale site of `S` has fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.affineSiteHasPullbacks X.toChosenBigSite S :
    HasPullbacks (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineSite X.toChosenBigSite S))

/- Lemma 61.12.10 (8): the functor from the chosen big affine pro-étale site of `S` to
schemes commutes with fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.affineToSchemePreservesPullbacks X.toChosenBigSite S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineToScheme X.toChosenBigSite S))

/- Lemma 61.12.10 (9): the chosen big pro-étale carrier has equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.carrierHasEqualizers X.toChosenBigSite X.specZ X.specZIso :
    HasEqualizers X.toChosenBigSite.carrier)

/- Lemma 61.12.10 (10): the functor from the chosen big pro-étale carrier to schemes
commutes with equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.toSchemePreservesEqualizers X.toChosenBigSite X.specZ X.specZIso :
    PreservesLimitsOfShape WalkingParallelPair X.toChosenBigSite.toScheme)

/- Lemma 61.12.10 (11): the chosen big pro-étale site of `S` has equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.bigSiteHasEqualizers X.toChosenBigSite S :
    HasEqualizers (AlgebraicGeometry.ChosenBigProetaleSite.bigSite X.toChosenBigSite S))

/- Lemma 61.12.10 (12): the functor from the chosen big pro-étale site of `S` to schemes
commutes with equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.bigToSchemePreservesEqualizers X.toChosenBigSite S :
    PreservesLimitsOfShape WalkingParallelPair
      (AlgebraicGeometry.ChosenBigProetaleSite.bigToScheme X.toChosenBigSite S))

/- Lemma 61.12.10 (13): the chosen small pro-étale site of `S` has equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallSiteHasEqualizers X.toChosenBigSite S :
    HasEqualizers (AlgebraicGeometry.ChosenBigProetaleSite.smallSite X.toChosenBigSite S))

/- Lemma 61.12.10 (14): the functor from the chosen small pro-étale site of `S` to
schemes commutes with equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallToSchemePreservesEqualizers X.toChosenBigSite S :
    PreservesLimitsOfShape WalkingParallelPair
      (AlgebraicGeometry.ChosenBigProetaleSite.smallToScheme X.toChosenBigSite S))

/- Lemma 61.12.10 (15): the identity object `S/S` is final in the chosen big pro-étale site. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.sliceIdentityTerminal X.toChosenBigSite S :
    IsTerminal (Over.mk (𝟙 S) :
      AlgebraicGeometry.ChosenBigProetaleSite.bigSite X.toChosenBigSite S))

/- Lemma 61.12.10 (16): the identity object `S/S` is final in the chosen small pro-étale site. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallTerminalObjectIsTerminal X.toChosenBigSite S :
    IsTerminal
      (AlgebraicGeometry.ChosenBigProetaleSite.smallTerminalObject X.toChosenBigSite S))

/- Lemma 61.12.10 (17): a represented `Spec (ULift ℤ)` is final in the chosen big
pro-étale carrier. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.carrierIsTerminal X.toChosenBigSite X.specZ X.specZIso :
    IsTerminal X.specZ)

/- Lemma 61.12.10 (18): that final object agrees with `Spec (ULift ℤ)` in the
category of schemes. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.WithSpecZ.specZIso X :
    X.toChosenBigSite.toScheme.obj X.specZ ≅ Spec (CommRingCat.of (ULift.{u} ℤ)))
