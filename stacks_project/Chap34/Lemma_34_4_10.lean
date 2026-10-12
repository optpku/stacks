/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ChosenPresentation.Limits
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u v

variable (X : AlgebraicGeometry.ChosenBigEtaleSite.{u, v})
  (S : X.carrier)

/- Lemma 34.4.10 (1): the carrier of the chosen big étale site has fibre products. -/
@[stacks 021D] #check
  (AlgebraicGeometry.ChosenBigEtaleSite.carrierHasPullbacks X :
    HasPullbacks X.carrier)

/- Lemma 34.4.10 (2): the functor from the chosen big étale carrier to schemes commutes
with fibre products. -/
@[stacks 021D] #check
  (AlgebraicGeometry.ChosenBigSite.toSchemePreservesPullbacks X :
    PreservesLimitsOfShape WalkingCospan X.toScheme)

/- Lemma 34.4.10 (3): the chosen big étale site of `S` has fibre products. -/
@[stacks 021D] #check
  (AlgebraicGeometry.ChosenBigSite.sliceHasPullbacks X S :
    HasPullbacks (AlgebraicGeometry.ChosenBigEtaleSite.bigSite X S))

/- Lemma 34.4.10 (4): the functor from the chosen big étale site of `S` to schemes
commutes with fibre products. -/
@[stacks 021D] #check
  (AlgebraicGeometry.ChosenBigSite.sliceToSchemePreservesPullbacks X S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigEtaleSite.bigToScheme X S))

/- Lemma 34.4.10 (5): the chosen small étale site of `S` has fibre products. -/
@[stacks 021D] #check
  (AlgebraicGeometry.ChosenBigEtaleSite.smallSiteHasPullbacks X S :
    HasPullbacks (AlgebraicGeometry.ChosenBigEtaleSite.smallSite X S))

/- Lemma 34.4.10 (6): the functor from the chosen small étale site of `S` to schemes
commutes with fibre products. -/
@[stacks 021D] #check
  (AlgebraicGeometry.ChosenBigEtaleSite.smallToSchemePreservesPullbacks X S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigEtaleSite.smallToScheme X S))

/- Lemma 34.4.10 (7): the chosen big affine étale site of `S` has fibre products. -/
@[stacks 021D] #check
  (AlgebraicGeometry.ChosenBigEtaleSite.bigAffineSiteHasPullbacks X S :
    HasPullbacks (AlgebraicGeometry.ChosenBigEtaleSite.bigAffineSite X S))

/- Lemma 34.4.10 (8): the functor from the chosen big affine étale site of `S` to schemes
commutes with fibre products. -/
@[stacks 021D] #check
  (AlgebraicGeometry.ChosenBigEtaleSite.bigAffineToSchemePreservesPullbacks X S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigEtaleSite.bigAffineToScheme X S))

/- Lemma 34.4.10 (9): the chosen small affine étale site of `S` has fibre products. -/
@[stacks 021D] #check
  (AlgebraicGeometry.ChosenBigEtaleSite.smallAffineSiteHasPullbacks X S :
    HasPullbacks (AlgebraicGeometry.ChosenBigEtaleSite.smallAffineSite X S))

/- Lemma 34.4.10 (10): the functor from the chosen small affine étale site of `S` to
schemes commutes with fibre products. -/
@[stacks 021D] #check
  (AlgebraicGeometry.ChosenBigEtaleSite.smallAffineToSchemePreservesPullbacks X S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigEtaleSite.smallAffineToScheme X S))

/- Lemma 34.4.10 (11): the identity object `S/S` is final in the chosen big étale site. -/
@[stacks 021D] #check
  (AlgebraicGeometry.ChosenBigEtaleSite.bigSiteIdentityTerminal X S :
    IsTerminal (Over.mk (𝟙 S) :
      AlgebraicGeometry.ChosenBigEtaleSite.bigSite X S))

/- Lemma 34.4.10 (12): the identity object `S/S` is final in the chosen small étale site. -/
@[stacks 021D] #check
  (AlgebraicGeometry.ChosenBigEtaleSite.smallTerminalObjectIsTerminal X S :
    IsTerminal
      (AlgebraicGeometry.ChosenBigEtaleSite.smallTerminalObject X S))
