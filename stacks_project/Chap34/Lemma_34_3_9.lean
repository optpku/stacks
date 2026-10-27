/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Chosen.Limits
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u v

variable (𝒮 : AlgebraicGeometry.SchAlphaBigSite.{u, v}
  AlgebraicGeometry.Scheme.zariskiPrecoverage)
  (S : 𝒮.carrier)

/- Lemma 34.3.9 (1): the chosen big Zariski carrier has fibre products. -/
@[stacks 020V] #check
  (AlgebraicGeometry.SchAlphaBigSite.carrierHasPullbacks 𝒮 :
    HasPullbacks 𝒮.carrier)

/- Lemma 34.3.9 (2): the functor from the chosen big Zariski carrier to schemes commutes
with fibre products. -/
@[stacks 020V] #check
  (AlgebraicGeometry.SchAlphaBigSite.toSchemePreservesPullbacks 𝒮 :
    PreservesLimitsOfShape WalkingCospan 𝒮.toScheme)

/- Lemma 34.3.9 (3): the chosen big Zariski site of `S` has fibre products. -/
@[stacks 020V] #check
  (AlgebraicGeometry.ChosenBigZariskiSite.bigSiteHasPullbacks 𝒮.toChosenBigSite S :
    HasPullbacks (AlgebraicGeometry.ChosenBigZariskiSite.bigSite 𝒮.toChosenBigSite S))

/- Lemma 34.3.9 (4): the functor from the chosen big Zariski site of `S` to schemes
commutes with fibre products. -/
@[stacks 020V] #check
  (AlgebraicGeometry.ChosenBigZariskiSite.bigToSchemePreservesPullbacks 𝒮.toChosenBigSite S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigZariskiSite.bigToScheme 𝒮.toChosenBigSite S))

/- Lemma 34.3.9 (5): the chosen small Zariski site of `S` has fibre products. -/
@[stacks 020V] #check
  (AlgebraicGeometry.ChosenBigZariskiSite.smallSiteHasPullbacks 𝒮.toChosenBigSite S :
    HasPullbacks (AlgebraicGeometry.ChosenBigZariskiSite.smallSite 𝒮.toChosenBigSite S))

/- Lemma 34.3.9 (6): the functor from the chosen small Zariski site of `S` to schemes
commutes with fibre products. -/
@[stacks 020V] #check
  (AlgebraicGeometry.ChosenBigZariskiSite.smallToSchemePreservesPullbacks 𝒮.toChosenBigSite S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigZariskiSite.smallToScheme 𝒮.toChosenBigSite S))

/- Lemma 34.3.9 (7): the chosen big affine Zariski site of `S` has fibre products. -/
@[stacks 020V] #check
  (AlgebraicGeometry.ChosenBigZariskiSite.bigAffineSiteHasPullbacks 𝒮.toChosenBigSite S :
    HasPullbacks (AlgebraicGeometry.ChosenBigZariskiSite.bigAffineSite 𝒮.toChosenBigSite S))

/- Lemma 34.3.9 (8): the functor from the chosen big affine Zariski site of `S` to
schemes commutes with fibre products. -/
@[stacks 020V] #check
  (AlgebraicGeometry.ChosenBigZariskiSite.bigAffineToSchemePreservesPullbacks 𝒮.toChosenBigSite S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigZariskiSite.bigAffineToScheme 𝒮.toChosenBigSite S))

/- Lemma 34.3.9 (9): the chosen small affine Zariski site of `S` has fibre products. -/
@[stacks 020V] #check
  (AlgebraicGeometry.ChosenBigZariskiSite.smallAffineSiteHasPullbacks 𝒮.toChosenBigSite S :
    HasPullbacks (AlgebraicGeometry.ChosenBigZariskiSite.smallAffineSite 𝒮.toChosenBigSite S))

/- Lemma 34.3.9 (10): the functor from the chosen small affine Zariski site of `S` to
schemes commutes with fibre products. -/
@[stacks 020V] #check
  (AlgebraicGeometry.ChosenBigZariskiSite.smallAffineToSchemePreservesPullbacks 𝒮.toChosenBigSite S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigZariskiSite.smallAffineToScheme 𝒮.toChosenBigSite S))

/- Lemma 34.3.9 (11): the identity object `S/S` is final in the chosen big Zariski site. -/
@[stacks 020V] #check
  (AlgebraicGeometry.ChosenBigZariskiSite.bigSiteIdentityTerminal 𝒮.toChosenBigSite S :
    IsTerminal (Over.mk (𝟙 S) :
      AlgebraicGeometry.ChosenBigZariskiSite.bigSite 𝒮.toChosenBigSite S))

/- Lemma 34.3.9 (12): the identity object `S/S` is final in the chosen small Zariski site. -/
@[stacks 020V] #check
  (AlgebraicGeometry.ChosenBigZariskiSite.smallTerminalObjectIsTerminal 𝒮.toChosenBigSite S :
    IsTerminal
      (AlgebraicGeometry.ChosenBigZariskiSite.smallTerminalObject 𝒮.toChosenBigSite S))
