module

import stacks_project.Chap61.Lemma_61_12_10_Limits
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

variable (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v})
  (S : X.carrier)
  (Z : X.carrier)
  (e : X.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ)))

/- Lemma 61.12.10 (1): the carrier of the chosen big pro-étale site has fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.carrierHasPullbacks X :
    HasPullbacks X.carrier)

/- Lemma 61.12.10 (2): the functor from the chosen big pro-étale carrier to schemes
commutes with fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.toSchemePreservesPullbacks X :
    PreservesLimitsOfShape WalkingCospan X.toScheme)

/- Lemma 61.12.10 (3): the chosen big pro-étale site of `S` has fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.sliceHasPullbacks X S :
    HasPullbacks (AlgebraicGeometry.ChosenBigProetaleSite.bigSite X S))

/- Lemma 61.12.10 (4): the functor from the chosen big pro-étale site of `S` to schemes
commutes with fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigSite.sliceToSchemePreservesPullbacks X S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigProetaleSite.bigToScheme X S))

/- Lemma 61.12.10 (5): the chosen small pro-étale site of `S` has fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallSiteHasPullbacks X S :
    HasPullbacks (AlgebraicGeometry.ChosenBigProetaleSite.smallSite X S))

/- Lemma 61.12.10 (6): the functor from the chosen small pro-étale site of `S` to schemes
commutes with fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallToSchemePreservesPullbacks X S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigProetaleSite.smallToScheme X S))

/- Lemma 61.12.10 (7): the chosen big affine pro-étale site of `S` has fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineSiteHasPullbacks X S :
    HasPullbacks (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineSite X S))

/- Lemma 61.12.10 (8): the functor from the chosen big affine pro-étale site of `S` to
schemes commutes with fibre products. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineToSchemePreservesPullbacks X S :
    PreservesLimitsOfShape WalkingCospan
      (AlgebraicGeometry.ChosenBigProetaleSite.bigAffineToScheme X S))

/- Lemma 61.12.10 (9): if the chosen big pro-étale carrier contains a represented
`Spec (ULift ℤ)`, then it has equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.carrierHasEqualizers X Z e :
    HasEqualizers X.carrier)

/- Lemma 61.12.10 (10): if the chosen big pro-étale carrier contains a represented
`Spec (ULift ℤ)`, then the functor to schemes commutes with equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.toSchemePreservesEqualizers X Z e :
    PreservesLimitsOfShape WalkingParallelPair X.toScheme)

/- Lemma 61.12.10 (11): the chosen big pro-étale site of `S` has equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.bigSiteHasEqualizers X S :
    HasEqualizers (AlgebraicGeometry.ChosenBigProetaleSite.bigSite X S))

/- Lemma 61.12.10 (12): the functor from the chosen big pro-étale site of `S` to schemes
commutes with equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.bigToSchemePreservesEqualizers X S :
    PreservesLimitsOfShape WalkingParallelPair
      (AlgebraicGeometry.ChosenBigProetaleSite.bigToScheme X S))

/- Lemma 61.12.10 (13): the chosen small pro-étale site of `S` has equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallSiteHasEqualizers X S :
    HasEqualizers (AlgebraicGeometry.ChosenBigProetaleSite.smallSite X S))

/- Lemma 61.12.10 (14): the functor from the chosen small pro-étale site of `S` to
schemes commutes with equalizers. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallToSchemePreservesEqualizers X S :
    PreservesLimitsOfShape WalkingParallelPair
      (AlgebraicGeometry.ChosenBigProetaleSite.smallToScheme X S))

/- Lemma 61.12.10 (15): the identity object `S/S` is final in the chosen big pro-étale site. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.bigSiteIdentityTerminal X S :
    IsTerminal (Over.mk (𝟙 S) :
      AlgebraicGeometry.ChosenBigProetaleSite.bigSite X S))

/- Lemma 61.12.10 (16): the identity object `S/S` is final in the chosen small pro-étale site. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.smallTerminalObjectIsTerminal X S :
    IsTerminal
      (AlgebraicGeometry.ChosenBigProetaleSite.smallTerminalObject X S))

/- Lemma 61.12.10 (17): a represented `Spec (ULift ℤ)` is final in the chosen big
pro-étale carrier. -/
@[stacks 098M] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.carrierIsTerminal X Z e :
    IsTerminal Z)

/- Lemma 61.12.10 (18): that final object agrees with `Spec (ULift ℤ)` in the
category of schemes. -/
@[stacks 098M] #check
  (e : X.toScheme.obj Z ≅ Spec (CommRingCat.of (ULift.{u} ℤ)))
