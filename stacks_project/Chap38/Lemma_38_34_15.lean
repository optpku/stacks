/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Affine
import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation
import StacksCheckRecall

open CategoryTheory

universe u v

variable (𝒮 : AlgebraicGeometry.ChosenBigHSite.{u, v}) (S : 𝒮.carrier)

/- Lemma 38.34.15 (1): the carrier of the chosen big h site has fibre products. -/
@[stacks 0EU3] #check
  (AlgebraicGeometry.ChosenBigSite.carrierHasPullbacks 𝒮 :
    Limits.HasPullbacks 𝒮.carrier)

/- Lemma 38.34.15 (2): the functor from the chosen big h carrier to schemes commutes
with fibre products. -/
@[stacks 0EU3] #check
  (AlgebraicGeometry.ChosenBigSite.toSchemePreservesPullbacks 𝒮 :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan 𝒮.toScheme)

/- Lemma 38.34.15 (3): the chosen big h site over `S` has fibre products. -/
@[stacks 0EU3] #check
  (AlgebraicGeometry.ChosenBigSite.sliceHasPullbacks 𝒮 S :
    Limits.HasPullbacks (Over S))

/- Lemma 38.34.15 (4): the source-scheme functor from the chosen big h site over `S`
commutes with fibre products. -/
@[stacks 0EU3] #check
  (AlgebraicGeometry.ChosenBigSite.sliceToSchemePreservesPullbacks 𝒮 S :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (AlgebraicGeometry.ChosenBigSite.sliceToScheme 𝒮 S))

/- Lemma 38.34.15 (5): the chosen big affine h site over `S` has fibre products. -/
@[stacks 0EU3] #check
  (AlgebraicGeometry.ChosenBigSite.affineSiteHasPullbacks 𝒮 S :
    Limits.HasPullbacks
      (AlgebraicGeometry.ChosenBigSite.affineSite 𝒮 S))

/- Lemma 38.34.15 (6): the source-scheme functor from the chosen big affine h site over
`S` commutes with fibre products. -/
@[stacks 0EU3] #check
  (AlgebraicGeometry.ChosenBigSite.affineToSchemePreservesPullbacks 𝒮 S :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (AlgebraicGeometry.ChosenBigSite.affineToScheme 𝒮 S))

/- Lemma 38.34.15 (7): the identity object `S/S` is final in the chosen big h slice. -/
@[stacks 0EU3] #check
  (AlgebraicGeometry.ChosenBigSite.sliceIdentityTerminal 𝒮 S :
    Limits.IsTerminal (Over.mk (𝟙 S) : Over S))
