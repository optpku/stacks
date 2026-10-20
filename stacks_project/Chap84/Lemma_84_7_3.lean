/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedHomology

/-!
# Lemma 84.7.3

Homology of `π_X^*` and `a_X^*` of a 3-term complex of quasi-coherent
`𝒪_X`-modules: the étale homology sheaf is `ε_{X,*}` of the fppf homology
sheaf, and both have vanishing positive cohomology on affine objects of
`(Spaces/X)_étale`.
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

/- Lemma 84.7.3 (1): `H_étale = ε_{X,*} H_fppf` as module sheaves on
`(Spaces/X)_étale`. -/
@[stacks 0DGQ] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.etaleHomology_pushforward :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : ShortComplex (Modules X))
    [K.X₁.IsQuasicoherent] [K.X₂.IsQuasicoherent] [K.X₃.IsQuasicoherent]
    [(Etale.Atlas.etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (etalePullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
        (etalePullbackShortComplex K).zero)]
    [HasKernel (fppfPullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (fppfPullbackShortComplex K).g (fppfPullbackShortComplex K).f
        (fppfPullbackShortComplex K).zero)],
    IsIsomorphic
      ((epsilonRingedHom X).modulePushforward.{u}.obj (fppfHomology K))
      (etaleHomology K))

/- Lemma 84.7.3 (2): `H^{p+1}_étale(U, H_étale) = 0` for every affine object
`U` of `(Spaces/X)_étale` and every `p : ℕ`. -/
@[stacks 0DGQ] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.etaleHomology_cohomology_isZero :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : ShortComplex (Modules X))
    [K.X₁.IsQuasicoherent] [K.X₂.IsQuasicoherent] [K.X₃.IsQuasicoherent]
    [(Etale.Atlas.etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (etalePullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
        (etalePullbackShortComplex K).zero)]
    [HasSheafify (Etale.Atlas.overEtaleRingedSite X).siteTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1}
      (Sheaf (Etale.Atlas.overEtaleRingedSite X).siteTopology AddCommGrpCat.{u + 1})]
    (U : Over X) [AlgebraicSpace.IsAffine U.left] (p : ℕ),
    IsZero
      ((Sheaf.cohomologyOverObjectFunctor.{u + 1, 0}
          (Etale.Atlas.overEtaleRingedSite X).siteTopology U (p + 1)).obj
        (etaleHomologyAb K)))

/- Lemma 84.7.3 (3): `H^{p+1}_fppf(U, H_fppf) = 0` for every affine object
`U` of `(Spaces/X)_étale` and every `p : ℕ`. -/
@[stacks 0DGQ] #check (AlgebraicGeometry.AlgebraicSpace.AssociatedModule.fppfHomology_cohomology_isZero :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
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
    (U : Over X) [AlgebraicSpace.IsAffine U.left] (p : ℕ),
    IsZero
      ((Sheaf.cohomologyOverObjectFunctor.{u + 1, 0}
          (overFppfRingedSite X).siteTopology U (p + 1)).obj
        (fppfHomologyAb K)))

end

end
