/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Refinement
import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Affine
import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.Limits
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

variable (B : AlgebraicGeometry.BigProetaleSite.{u}) (S : B.carrier)

/- Use the original bounded small carrier. The integer-spectrum representation
is constructed from its empty-diagram limit, rather than assumed as input. -/
@[stacks 098M] #check
  (B.exists_specZ : ∃ Z : B.carrier,
    Nonempty (B.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ))))

/- Lemma 61.12.10 (1): the carrier of the chosen big pro-étale site has fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.carrierHasPullbacks B.toChosenBigSite :
    HasPullbacks B.toChosenBigSite.carrier)

/- Lemma 61.12.10 (2): the functor from the chosen big pro-étale carrier to schemes
commutes with fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.toSchemePreservesPullbacks B.toChosenBigSite :
    PreservesLimitsOfShape WalkingCospan B.toChosenBigSite.toScheme)

/- Lemma 61.12.10 (3): the chosen big pro-étale site of `S` has fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.sliceHasPullbacks B.toChosenBigSite S :
    HasPullbacks (AlgebraicGeometry.ChosenBigProetaleSite.bigSite B.toChosenBigSite S))

/- Lemma 61.12.10 (4): the functor from the chosen big pro-étale site of `S` to schemes
commutes with fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.sliceToSchemePreservesPullbacks B.toChosenBigSite S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigProetaleSite.bigToScheme B.toChosenBigSite S))

/- Lemma 61.12.10 (5): the chosen small pro-étale site of `S` has fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallSiteHasPullbacks B.toChosenBigSite S :
    HasPullbacks (AlgebraicGeometry.ChosenBigProetaleSite.smallSite B.toChosenBigSite S))

/- Lemma 61.12.10 (6): the functor from the chosen small pro-étale site of `S` to schemes
commutes with fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallToSchemePreservesPullbacks B.toChosenBigSite S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigProetaleSite.smallToScheme B.toChosenBigSite S))

/- Lemma 61.12.10 (7): the chosen big affine pro-étale site of `S` has fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.affineSiteHasPullbacks B.toChosenBigSite S :
    HasPullbacks (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineSite B.toChosenBigSite S))

/- Lemma 61.12.10 (8): the functor from the chosen big affine pro-étale site of `S` to
schemes commutes with fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.affineToSchemePreservesPullbacks B.toChosenBigSite S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineToScheme B.toChosenBigSite S))

/- Lemma 61.12.10 (9): the chosen big pro-étale carrier has equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.carrierHasEqualizers B.toChosenBigSite B.specZ B.specZIso :
    HasEqualizers B.toChosenBigSite.carrier)

/- Lemma 61.12.10 (10): the functor from the chosen big pro-étale carrier to schemes
commutes with equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.toSchemePreservesEqualizers B.toChosenBigSite B.specZ B.specZIso :
    PreservesLimitsOfShape WalkingParallelPair B.toChosenBigSite.toScheme)

/- Lemma 61.12.10 (11): the chosen big pro-étale site of `S` has equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.bigSiteHasEqualizers B.toChosenBigSite S :
    HasEqualizers (AlgebraicGeometry.ChosenBigProetaleSite.bigSite B.toChosenBigSite S))

/- Lemma 61.12.10 (12): the functor from the chosen big pro-étale site of `S` to schemes
commutes with equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.bigToSchemePreservesEqualizers B.toChosenBigSite S :
    PreservesLimitsOfShape WalkingParallelPair
      (AlgebraicGeometry.ChosenBigProetaleSite.bigToScheme B.toChosenBigSite S))

/- Lemma 61.12.10 (13): the chosen small pro-étale site of `S` has equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallSiteHasEqualizers B.toChosenBigSite S :
    HasEqualizers (AlgebraicGeometry.ChosenBigProetaleSite.smallSite B.toChosenBigSite S))

/- Lemma 61.12.10 (14): the functor from the chosen small pro-étale site of `S` to
schemes commutes with equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallToSchemePreservesEqualizers B.toChosenBigSite S :
    PreservesLimitsOfShape WalkingParallelPair
      (AlgebraicGeometry.ChosenBigProetaleSite.smallToScheme B.toChosenBigSite S))

/- Lemma 61.12.10 (15): the identity object `S/S` is final in the chosen big pro-étale site. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.sliceIdentityTerminal B.toChosenBigSite S :
    IsTerminal (Over.mk (𝟙 S) :
      AlgebraicGeometry.ChosenBigProetaleSite.bigSite B.toChosenBigSite S))

/- Lemma 61.12.10 (16): the identity object `S/S` is final in the chosen small pro-étale site. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallTerminalObjectIsTerminal B.toChosenBigSite S :
    IsTerminal
      (AlgebraicGeometry.ChosenBigProetaleSite.smallTerminalObject B.toChosenBigSite S))

/- Lemma 61.12.10 (17): a represented `Spec (ULift ℤ)` is final in the chosen big
pro-étale carrier. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.carrierIsTerminal B.toChosenBigSite B.specZ B.specZIso :
    IsTerminal B.specZ)

/- Lemma 61.12.10 (18): that final object agrees with `Spec (ULift ℤ)` in the
category of schemes. -/
@[stacks 098M] #check
  (B.specZIso : B.toScheme.obj B.specZ ≅ Spec (CommRingCat.of (ULift.{u} ℤ)))
