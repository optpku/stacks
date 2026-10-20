module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.MapAnnihilation
import StacksCheckRecall

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CoherentFormalMap

noncomputable section

universe u

/- Remark 76.42.7: for a morphism of coherent formal modules on a Noetherian algebraic
space, uniform annihilation of all positive-stage kernels and cokernels, annihilation of
the corresponding completed maps on every affine étale chart, and annihilation on some
surjective affine étale chart are equivalent. When this holds, α is a map whose kernel
and cokernel are annihilated by a power of K. -/
@[stacks 08BA] #check
  (AlgebraicGeometry.AlgebraicSpace.CoherentFormalMap.kernelCokernelAnnihilation_tfae :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      (I K : IdealSubobject X) [IsQuasiCoherent I] [IsQuasiCoherent K]
      {F G : CoherentFormalModules X I} (alpha : F ⟶ G)
      (M N : (U : affineEtaleSite X) →
        FGModuleCat
          (AdicCompletion (idealOnEtaleChart I U.obj)
            ((commStructureSheaf X).obj.obj (op U.obj))))
      [(U : affineEtaleSite X) →
        Module ((commStructureSheaf X).obj.obj (op U.obj)) (M U).obj]
      [(U : affineEtaleSite X) →
        IsScalarTower ((commStructureSheaf X).obj.obj (op U.obj))
          (AdicCompletion (idealOnEtaleChart I U.obj)
            ((commStructureSheaf X).obj.obj (op U.obj))) (M U).obj]
      [(U : affineEtaleSite X) →
        IsAdicComplete (idealOnEtaleChart I U.obj) (M U).obj]
      [(U : affineEtaleSite X) →
        Module ((commStructureSheaf X).obj.obj (op U.obj)) (N U).obj]
      [(U : affineEtaleSite X) →
        IsScalarTower ((commStructureSheaf X).obj.obj (op U.obj))
          (AdicCompletion (idealOnEtaleChart I U.obj)
            ((commStructureSheaf X).obj.obj (op U.obj))) (N U).obj]
      [(U : affineEtaleSite X) →
        IsAdicComplete (idealOnEtaleChart I U.obj) (N U).obj]
      (completedMap : (U : affineEtaleSite X) →
        (M U).obj →ₗ[AdicCompletion (idealOnEtaleChart I U.obj)
            ((commStructureSheaf X).obj.obj (op U.obj))] (N U).obj)
      (sourceEquiv : (U : affineEtaleSite X) → (n : ℕ+) →
        ((M U).obj ⧸
            idealOnEtaleChart I U.obj ^ (n : ℕ) •
              (⊤ : Submodule ((commStructureSheaf X).obj.obj (op U.obj))
                (M U).obj)) ≃ₗ[(commStructureSheaf X).obj.obj (op U.obj)]
          (((F.obj).obj (op (n : ℕ))).obj.val.obj (op U.obj)))
      (targetEquiv : (U : affineEtaleSite X) → (n : ℕ+) →
        ((N U).obj ⧸
            idealOnEtaleChart I U.obj ^ (n : ℕ) •
              (⊤ : Submodule ((commStructureSheaf X).obj.obj (op U.obj))
                (N U).obj)) ≃ₗ[(commStructureSheaf X).obj.obj (op U.obj)]
          (((G.obj).obj (op (n : ℕ))).obj.val.obj (op U.obj)))
      (presentation :
        CoherentFormalMap.IsEtaleAffineStagePresentation I alpha M N completedMap
          sourceEquiv targetEquiv),
      List.TFAE [
        CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation K alpha,
        CoherentFormalMap.AffineMapsHaveKernelCokernelAnnihilation I K M N
          completedMap,
        CoherentFormalMap.ExistsCoveringAffineMapHaveKernelCokernelAnnihilation
          I K M N completedMap
      ])
