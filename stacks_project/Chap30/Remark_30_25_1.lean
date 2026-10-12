/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.MapAnnihilation

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

/- Remark 30.25.1: for a morphism of coherent formal modules, uniform annihilation of all
positive-stage kernels and cokernels, affine-local annihilation of the corresponding completed
maps, and annihilation on a finite affine open cover are equivalent. -/
@[stacks 0888] #check
  (AlgebraicGeometry.Scheme.CoherentFormalMap.kernelCokernelAnnihilation_tfae :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
      {F G : Scheme.CoherentFormalModules X I} (alpha : F ⟶ G)
      (M N : (U : X.affineOpens) →
        FGModuleCat (AdicCompletion (I.ideal U) Γ(X, U.1)))
      [(U : X.affineOpens) → Module Γ(X, U.1) (M U).obj]
      [(U : X.affineOpens) →
        IsScalarTower Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)) (M U).obj]
      [(U : X.affineOpens) → IsAdicComplete (I.ideal U) (M U).obj]
      [(U : X.affineOpens) → Module Γ(X, U.1) (N U).obj]
      [(U : X.affineOpens) →
        IsScalarTower Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)) (N U).obj]
      [(U : X.affineOpens) → IsAdicComplete (I.ideal U) (N U).obj]
      (completedMap : (U : X.affineOpens) →
        (M U).obj →ₗ[AdicCompletion (I.ideal U) Γ(X, U.1)] (N U).obj)
      (sourceEquiv : (U : X.affineOpens) → (n : ℕ+) →
        ((M U).obj ⧸
            I.ideal U ^ (n : ℕ) • (⊤ : Submodule Γ(X, U.1) (M U).obj)) ≃ₗ[Γ(X, U.1)]
          (((F.obj).obj (op (n : ℕ))).obj.val.obj (op U.1)))
      (targetEquiv : (U : X.affineOpens) → (n : ℕ+) →
        ((N U).obj ⧸
            I.ideal U ^ (n : ℕ) • (⊤ : Submodule Γ(X, U.1) (N U).obj)) ≃ₗ[Γ(X, U.1)]
          (((G.obj).obj (op (n : ℕ))).obj.val.obj (op U.1)))
      (presentation :
        Scheme.CoherentFormalMap.IsAffineStagePresentation
          I alpha M N completedMap sourceEquiv targetEquiv),
      List.TFAE [
        Scheme.CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation K alpha,
        Scheme.CoherentFormalMap.AffineMapsHaveKernelCokernelAnnihilation
          I K M N completedMap,
        Scheme.CoherentFormalMap.AffineMapsHaveKernelCokernelAnnihilationOnFiniteCover
          I K M N completedMap
      ])
