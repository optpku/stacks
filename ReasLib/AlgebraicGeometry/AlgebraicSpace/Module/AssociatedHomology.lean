/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Ringed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise

/-!
# Homology of pulled-back quasi-coherent short complexes

Termwise pullback to the big étale and fppf ringed sites gives homology
sheaves as cokernels of the canonical maps into kernels. These sheaves
are compared by direct image and have zero positive cohomology on affine objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Fppf
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AssociatedModule

variable {S : Scheme.{u}}

/-- `π_X^*` of a 3-term complex of `𝒪_X`-modules, as a short complex on
`(Spaces/X)_étale`. -/
def etalePullbackShortComplex {X : AlgebraicSpace S} (K : ShortComplex (Modules X))
    [(Etale.Atlas.etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    ShortComplex (RingedSite.ModuleCat.{u} (Etale.Atlas.overEtaleRingedSite X)) :=
  ((Etale.Atlas.etalePiRingedHom X).modulePullback.{u}).mapShortComplex.obj K

/-- The first term of `etalePullbackShortComplex K` is `π_X^* K.X₁`. -/
theorem etalePullbackShortComplex_X₁ {X : AlgebraicSpace S}
    (K : ShortComplex (Modules X))
    [(Etale.Atlas.etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    (etalePullbackShortComplex K).X₁ =
      (Etale.Atlas.etalePiRingedHom X).modulePullback.{u}.obj K.X₁ :=
  rfl

/-- The middle term of `etalePullbackShortComplex K` is `π_X^* K.X₂`. -/
theorem etalePullbackShortComplex_X₂ {X : AlgebraicSpace S}
    (K : ShortComplex (Modules X))
    [(Etale.Atlas.etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    (etalePullbackShortComplex K).X₂ =
      (Etale.Atlas.etalePiRingedHom X).modulePullback.{u}.obj K.X₂ :=
  rfl

/-- The last term of `etalePullbackShortComplex K` is `π_X^* K.X₃`. -/
theorem etalePullbackShortComplex_X₃ {X : AlgebraicSpace S}
    (K : ShortComplex (Modules X))
    [(Etale.Atlas.etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    (etalePullbackShortComplex K).X₃ =
      (Etale.Atlas.etalePiRingedHom X).modulePullback.{u}.obj K.X₃ :=
  rfl

/-- `a_X^*` of a 3-term complex of `𝒪_X`-modules, as a short complex on
`(Spaces/X)_fppf`. -/
def fppfPullbackShortComplex {X : AlgebraicSpace S} (K : ShortComplex (Modules X))
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    ShortComplex (RingedSite.ModuleCat.{u} (overFppfRingedSite X)) :=
  ((aRingedHom X).modulePullback.{u}).mapShortComplex.obj K

/-- The first term of `fppfPullbackShortComplex K` is `a_X^* K.X₁`. -/
theorem fppfPullbackShortComplex_X₁ {X : AlgebraicSpace S}
    (K : ShortComplex (Modules X))
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    (fppfPullbackShortComplex K).X₁ =
      (aRingedHom X).modulePullback.{u}.obj K.X₁ :=
  rfl

/-- The middle term of `fppfPullbackShortComplex K` is `a_X^* K.X₂`. -/
theorem fppfPullbackShortComplex_X₂ {X : AlgebraicSpace S}
    (K : ShortComplex (Modules X))
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    (fppfPullbackShortComplex K).X₂ =
      (aRingedHom X).modulePullback.{u}.obj K.X₂ :=
  rfl

/-- The last term of `fppfPullbackShortComplex K` is `a_X^* K.X₃`. -/
theorem fppfPullbackShortComplex_X₃ {X : AlgebraicSpace S}
    (K : ShortComplex (Modules X))
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    (fppfPullbackShortComplex K).X₃ =
      (aRingedHom X).modulePullback.{u}.obj K.X₃ :=
  rfl

/-- Homology sheaf of `π_X^* K` on `(Spaces/X)_étale`, as
`ker(π_X^* K.X₂ ⟶ π_X^* K.X₃) / im(π_X^* K.X₁ ⟶ π_X^* K.X₂)`. -/
def etaleHomology {X : AlgebraicSpace S} (K : ShortComplex (Modules X))
    [(Etale.Atlas.etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (etalePullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
        (etalePullbackShortComplex K).zero)] :
    RingedSite.ModuleCat.{u} (Etale.Atlas.overEtaleRingedSite X) :=
  cokernel
    (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
      (etalePullbackShortComplex K).zero)

/-- `etaleHomology K` is the cokernel of the canonical map from `π_X^* K.X₁`
into `ker(π_X^* K.X₂ ⟶ π_X^* K.X₃)`. -/
theorem etaleHomology_eq {X : AlgebraicSpace S} (K : ShortComplex (Modules X))
    [(Etale.Atlas.etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (etalePullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
        (etalePullbackShortComplex K).zero)] :
    etaleHomology K =
      cokernel
        (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
          (etalePullbackShortComplex K).zero) :=
  rfl

/-- Homology sheaf of `a_X^* K` on `(Spaces/X)_fppf`, as
`ker(a_X^* K.X₂ ⟶ a_X^* K.X₃) / im(a_X^* K.X₁ ⟶ a_X^* K.X₂)`. -/
def fppfHomology {X : AlgebraicSpace S} (K : ShortComplex (Modules X))
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (fppfPullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (fppfPullbackShortComplex K).g (fppfPullbackShortComplex K).f
        (fppfPullbackShortComplex K).zero)] :
    RingedSite.ModuleCat.{u} (overFppfRingedSite X) :=
  cokernel
    (kernel.lift (fppfPullbackShortComplex K).g (fppfPullbackShortComplex K).f
      (fppfPullbackShortComplex K).zero)

/-- `fppfHomology K` is the cokernel of the canonical map from `a_X^* K.X₁`
into `ker(a_X^* K.X₂ ⟶ a_X^* K.X₃)`. -/
theorem fppfHomology_eq {X : AlgebraicSpace S} (K : ShortComplex (Modules X))
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (fppfPullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (fppfPullbackShortComplex K).g (fppfPullbackShortComplex K).f
        (fppfPullbackShortComplex K).zero)] :
    fppfHomology K =
      cokernel
        (kernel.lift (fppfPullbackShortComplex K).g (fppfPullbackShortComplex K).f
          (fppfPullbackShortComplex K).zero) :=
  rfl

/-- Underlying abelian sheaf of the carrier-lifted étale homology sheaf. -/
def etaleHomologyAb {X : AlgebraicSpace S} (K : ShortComplex (Modules X))
    [(Etale.Atlas.etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (etalePullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
        (etalePullbackShortComplex K).zero)] :
    Sheaf (Etale.Atlas.overEtaleRingedSite X).siteTopology AddCommGrpCat.{u + 1} :=
  (SheafOfModules.toSheaf (Etale.Atlas.overEtaleRingedSite X).structureSheaf).obj
    (RingedSite.Module.carrierLift (Etale.Atlas.overEtaleRingedSite X) (etaleHomology K))

/-- `etaleHomologyAb K` is `toSheaf` of the carrier lift of `etaleHomology K`. -/
theorem etaleHomologyAb_eq {X : AlgebraicSpace S} (K : ShortComplex (Modules X))
    [(Etale.Atlas.etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (etalePullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
        (etalePullbackShortComplex K).zero)] :
    etaleHomologyAb K =
      (SheafOfModules.toSheaf (Etale.Atlas.overEtaleRingedSite X).structureSheaf).obj
        (RingedSite.Module.carrierLift (Etale.Atlas.overEtaleRingedSite X) (etaleHomology K)) :=
  rfl

/-- Underlying abelian sheaf of the carrier-lifted fppf homology sheaf. -/
def fppfHomologyAb {X : AlgebraicSpace S} (K : ShortComplex (Modules X))
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (fppfPullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (fppfPullbackShortComplex K).g (fppfPullbackShortComplex K).f
        (fppfPullbackShortComplex K).zero)] :
    Sheaf (overFppfRingedSite X).siteTopology AddCommGrpCat.{u + 1} :=
  (SheafOfModules.toSheaf (overFppfRingedSite X).structureSheaf).obj
    (RingedSite.Module.carrierLift (overFppfRingedSite X) (fppfHomology K))

/-- `fppfHomologyAb K` is `toSheaf` of the carrier lift of `fppfHomology K`. -/
theorem fppfHomologyAb_eq {X : AlgebraicSpace S} (K : ShortComplex (Modules X))
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (fppfPullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (fppfPullbackShortComplex K).g (fppfPullbackShortComplex K).f
        (fppfPullbackShortComplex K).zero)] :
    fppfHomologyAb K =
      (SheafOfModules.toSheaf (overFppfRingedSite X).structureSheaf).obj
        (RingedSite.Module.carrierLift (overFppfRingedSite X) (fppfHomology K)) :=
  rfl

/-- Pushing the fppf homology sheaf of `a_X^* K` forward along `ε_X` recovers
the étale homology sheaf of `π_X^* K`. -/
theorem etaleHomology_pushforward {X : AlgebraicSpace S}
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
    [(Etale.Atlas.etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (etalePullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
        (etalePullbackShortComplex K).zero)]
    [HasSheafify (Etale.Atlas.overEtaleRingedSite X).siteTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1}
      (Sheaf (Etale.Atlas.overEtaleRingedSite X).siteTopology AddCommGrpCat.{u + 1})]
    (U : Over X) [AlgebraicSpace.IsAffine U.left] (p : ℕ) :
    IsZero
      ((Sheaf.cohomologyOverObjectFunctor.{u + 1, 0}
          (Etale.Atlas.overEtaleRingedSite X).siteTopology U (p + 1)).obj
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
