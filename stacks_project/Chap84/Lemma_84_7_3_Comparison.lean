module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap84.Lemma_84_7_3_Homology

/-!
# Homology comparison along `ε_X` and affine vanishing

The étale homology sheaf of `π_X^* K` is `ε_{X,*}` of the fppf homology
sheaf of `a_X^* K`, and both have vanishing positive cohomology on every
affine object of `(Spaces/X)_étale`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.AssociatedModule
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Fppf
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AssociatedModule

variable {S : Scheme.{u}}

/-- Pushing the fppf homology sheaf of `a_X^* K` forward along `ε_X` recovers
the étale homology sheaf of `π_X^* K`. -/
theorem etaleHomology_pushforward {X : AlgebraicSpace S}
    (K : ShortComplex (Modules X))
    [K.X₁.IsQuasicoherent] [K.X₂.IsQuasicoherent] [K.X₃.IsQuasicoherent]
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (etalePullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
        (etalePullbackShortComplex K).zero)]
    [HasKernel (fppfPullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (fppfPullbackShortComplex K).g (fppfPullbackShortComplex K).f
        (fppfPullbackShortComplex K).zero)] :
    IsIsomorphic
      ((epsilonRingedHom X).modulePushforward.{u}.obj (fppfHomology K))
      (etaleHomology K) :=
  sorry

/-- Positive étale cohomology of the étale homology sheaf vanishes on every
affine object of `(Spaces/X)_étale`. -/
theorem etaleHomology_cohomology_isZero {X : AlgebraicSpace S}
    (K : ShortComplex (Modules X))
    [K.X₁.IsQuasicoherent] [K.X₂.IsQuasicoherent] [K.X₃.IsQuasicoherent]
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (etalePullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
        (etalePullbackShortComplex K).zero)]
    [HasSheafify (overEtaleRingedSite X).siteTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1}
      (Sheaf (overEtaleRingedSite X).siteTopology AddCommGrpCat.{u + 1})]
    (U : Over X) [AlgebraicSpace.IsAffine U.left] (p : ℕ) :
    IsZero
      ((Sheaf.cohomologyOverObjectFunctor.{u + 1, 0}
          (overEtaleRingedSite X).siteTopology U (p + 1)).obj
        (etaleHomologyAb K)) :=
  sorry

/-- Positive fppf cohomology of the fppf homology sheaf vanishes on every
affine object of `(Spaces/X)_étale`. -/
theorem fppfHomology_cohomology_isZero {X : AlgebraicSpace S}
    (K : ShortComplex (Modules X))
    [K.X₁.IsQuasicoherent] [K.X₂.IsQuasicoherent] [K.X₃.IsQuasicoherent]
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (fppfPullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (fppfPullbackShortComplex K).g (fppfPullbackShortComplex K).f
        (fppfPullbackShortComplex K).zero)]
    [HasSheafify (overFppfRingedSite X).siteTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1}
      (Sheaf (overFppfRingedSite X).siteTopology AddCommGrpCat.{u + 1})]
    (U : Over X) [AlgebraicSpace.IsAffine U.left] (p : ℕ) :
    IsZero
      ((Sheaf.cohomologyOverObjectFunctor.{u + 1, 0}
          (overFppfRingedSite X).siteTopology U (p + 1)).obj
        (fppfHomologyAb K)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AssociatedModule

end

end
