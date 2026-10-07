module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import stacks_project.Chap84.Lemma_84_7_1_Carrier
public import stacks_project.Chap84.Lemma_84_7_1_Ringed

/-!
# Homology of pulled-back quasi-coherent short complexes

Termwise `π_X^*` and `a_X^*` of a 3-term complex of `𝒪_X`-modules, and the
homology sheaves `ker(g)/im(f)` as cokernels of `kernel.lift` on
`(Spaces/X)_étale` and `(Spaces/X)_fppf`.
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

/-- `π_X^*` preserves zero morphisms, so it acts on short complexes. -/
instance etalePi_modulePullback_preservesZeroMorphisms (X : AlgebraicSpace S)
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    ((etalePiRingedHom X).modulePullback.{u}).PreservesZeroMorphisms :=
  sorry

/-- `a_X^*` preserves zero morphisms, so it acts on short complexes. -/
instance aRingedHom_modulePullback_preservesZeroMorphisms (X : AlgebraicSpace S)
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    ((aRingedHom X).modulePullback.{u}).PreservesZeroMorphisms :=
  sorry

/-- `π_X^*` of a 3-term complex of `𝒪_X`-modules, as a short complex on
`(Spaces/X)_étale`. -/
def etalePullbackShortComplex {X : AlgebraicSpace S} (K : ShortComplex (Modules X))
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    ShortComplex (RingedSite.ModuleCat.{u} (overEtaleRingedSite X)) :=
  ((etalePiRingedHom X).modulePullback.{u}).mapShortComplex.obj K

/-- The first term of `etalePullbackShortComplex K` is `π_X^* K.X₁`. -/
theorem etalePullbackShortComplex_X₁ {X : AlgebraicSpace S}
    (K : ShortComplex (Modules X))
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    (etalePullbackShortComplex K).X₁ =
      (etalePiRingedHom X).modulePullback.{u}.obj K.X₁ :=
  rfl

/-- The middle term of `etalePullbackShortComplex K` is `π_X^* K.X₂`. -/
theorem etalePullbackShortComplex_X₂ {X : AlgebraicSpace S}
    (K : ShortComplex (Modules X))
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    (etalePullbackShortComplex K).X₂ =
      (etalePiRingedHom X).modulePullback.{u}.obj K.X₂ :=
  rfl

/-- The last term of `etalePullbackShortComplex K` is `π_X^* K.X₃`. -/
theorem etalePullbackShortComplex_X₃ {X : AlgebraicSpace S}
    (K : ShortComplex (Modules X))
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    (etalePullbackShortComplex K).X₃ =
      (etalePiRingedHom X).modulePullback.{u}.obj K.X₃ :=
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
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (etalePullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
        (etalePullbackShortComplex K).zero)] :
    RingedSite.ModuleCat.{u} (overEtaleRingedSite X) :=
  cokernel
    (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
      (etalePullbackShortComplex K).zero)

/-- `etaleHomology K` is the cokernel of the canonical map from `π_X^* K.X₁`
into `ker(π_X^* K.X₂ ⟶ π_X^* K.X₃)`. -/
theorem etaleHomology_eq {X : AlgebraicSpace S} (K : ShortComplex (Modules X))
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (etalePullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
        (etalePullbackShortComplex K).zero)] :
    etaleHomology K =
      cokernel
        (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
          (etalePullbackShortComplex K).zero) :=
  rfl

/-- When the pulled-back short complex has homology, `etaleHomology K` recovers
`ShortComplex.homology`. -/
theorem etaleHomology_isoCokernelLift {X : AlgebraicSpace S}
    (K : ShortComplex (Modules X))
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (etalePullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
        (etalePullbackShortComplex K).zero)]
    [(etalePullbackShortComplex K).HasHomology] :
    IsIsomorphic (etaleHomology K) (etalePullbackShortComplex K).homology :=
  sorry

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

/-- When the pulled-back short complex has homology, `fppfHomology K` recovers
`ShortComplex.homology`. -/
theorem fppfHomology_isoCokernelLift {X : AlgebraicSpace S}
    (K : ShortComplex (Modules X))
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (fppfPullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (fppfPullbackShortComplex K).g (fppfPullbackShortComplex K).f
        (fppfPullbackShortComplex K).zero)]
    [(fppfPullbackShortComplex K).HasHomology] :
    IsIsomorphic (fppfHomology K) (fppfPullbackShortComplex K).homology :=
  sorry

/-- Underlying abelian sheaf of the carrier-lifted étale homology sheaf. -/
def etaleHomologyAb {X : AlgebraicSpace S} (K : ShortComplex (Modules X))
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (etalePullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
        (etalePullbackShortComplex K).zero)] :
    Sheaf (overEtaleRingedSite X).siteTopology AddCommGrpCat.{u + 1} :=
  (SheafOfModules.toSheaf (overEtaleRingedSite X).structureSheaf).obj
    (moduleCarrierLift (overEtaleRingedSite X) (etaleHomology K))

/-- `etaleHomologyAb K` is `toSheaf` of the carrier lift of `etaleHomology K`. -/
theorem etaleHomologyAb_eq {X : AlgebraicSpace S} (K : ShortComplex (Modules X))
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (etalePullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (etalePullbackShortComplex K).g (etalePullbackShortComplex K).f
        (etalePullbackShortComplex K).zero)] :
    etaleHomologyAb K =
      (SheafOfModules.toSheaf (overEtaleRingedSite X).structureSheaf).obj
        (moduleCarrierLift (overEtaleRingedSite X) (etaleHomology K)) :=
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
    (moduleCarrierLift (overFppfRingedSite X) (fppfHomology K))

/-- `fppfHomologyAb K` is `toSheaf` of the carrier lift of `fppfHomology K`. -/
theorem fppfHomologyAb_eq {X : AlgebraicSpace S} (K : ShortComplex (Modules X))
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [HasKernel (fppfPullbackShortComplex K).g]
    [HasCokernel
      (kernel.lift (fppfPullbackShortComplex K).g (fppfPullbackShortComplex K).f
        (fppfPullbackShortComplex K).zero)] :
    fppfHomologyAb K =
      (SheafOfModules.toSheaf (overFppfRingedSite X).structureSheaf).obj
        (moduleCarrierLift (overFppfRingedSite X) (fppfHomology K)) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.AssociatedModule

end

end
