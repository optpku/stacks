module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPowerAnnihilation

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal
public import ReasLib.LinearAlgebra.QuotientByIdeal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealQuotient

/-!
# Kernel and cokernel annihilation for coherent formal module morphisms

Uniform ideal-power annihilation of positive-stage kernels and cokernels is
equivalent to annihilation of completed maps on affine étale charts.
Section ideals and commuting quotient presentations relate the stage maps to
the completed maps.
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The ideal of sections of an ideal sheaf on an object of the small étale site. -/
noncomputable def idealOnEtaleChart {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : smallEtaleSite X) :
    Ideal ((commStructureSheaf X).obj.obj (op U)) :=
  IdealSheaf.sections (Modules.toCommSubobject I) (op U)

/-- The étale-chart section ideal is the ordinary section ideal of the recast
ideal sheaf. -/
theorem idealOnEtaleChart_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : smallEtaleSite X) :
    idealOnEtaleChart I U =
      IdealSheaf.sections (Modules.toCommSubobject I) (op U) :=
  sorry

/-- Membership in the étale-chart section ideal is witnessed by a local section of
the recast ideal sheaf. -/
theorem mem_idealOnEtaleChart {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : smallEtaleSite X)
    (x : (commStructureSheaf X).obj.obj (op U)) :
    x ∈ idealOnEtaleChart I U ↔
      ∃ s : (Modules.toCommSubobject I :
          RingedSite.ModuleCat.{u} (commRingedSite X)).val.obj (op U),
        SheafOfModules.Subobject.inclusionApp (Modules.toCommSubobject I) (op U) s =
          x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.CoherentFormalMap

/-- One positive power of an ideal sheaf annihilates the kernels and cokernels
of every positive stage of a morphism of coherent formal modules. -/
def StagesHaveUniformKernelCokernelAnnihilation
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X} [IsQuasiCoherent I]
    (K : IdealSubobject X) {E F : CoherentFormalModules X I}
    (alpha : E ⟶ F) : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ+,
    Modules.IsAnnihilatedByIdealPower K
        (kernel ((Coh.inclusion X).map (alpha.hom.app (op (n : ℕ))))) t ∧
      Modules.IsAnnihilatedByIdealPower K
        (cokernel ((Coh.inclusion X).map (alpha.hom.app (op (n : ℕ))))) t

/-- Uniform annihilation means that one positive power annihilates both kernels
and cokernels at all positive stages. -/
theorem stagesHaveUniformKernelCokernelAnnihilation_iff
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X} [IsQuasiCoherent I]
    (K : IdealSubobject X) {E F : CoherentFormalModules X I}
    (alpha : E ⟶ F) :
    StagesHaveUniformKernelCokernelAnnihilation K alpha ↔
      ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ+,
        Modules.IsAnnihilatedByIdealPower K
            (kernel ((Coh.inclusion X).map (alpha.hom.app (op (n : ℕ))))) t ∧
          Modules.IsAnnihilatedByIdealPower K
            (cokernel ((Coh.inclusion X).map (alpha.hom.app (op (n : ℕ))))) t :=
  Iff.rfl

/-- Explicit affine completed modules and their maps present the stages of a
coherent-formal morphism when the quotient maps commute with the supplied
identifications at every positive stage on every affine étale chart. -/
def IsEtaleAffineStagePresentation
    {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
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
      Module ((commStructureSheaf X).obj.obj (op U.obj)) (N U).obj]
    [(U : affineEtaleSite X) →
      IsScalarTower ((commStructureSheaf X).obj.obj (op U.obj))
        (AdicCompletion (idealOnEtaleChart I U.obj)
          ((commStructureSheaf X).obj.obj (op U.obj))) (N U).obj]
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
        (((G.obj).obj (op (n : ℕ))).obj.val.obj (op U.obj))) : Prop :=
  ∀ (U : affineEtaleSite X) (n : ℕ+),
    (targetEquiv U n).toLinearMap.comp
        (((completedMap U).restrictScalars
            ((commStructureSheaf X).obj.obj (op U.obj))).quotientMapByIdealPower
          (idealOnEtaleChart I U.obj) n) =
      (((alpha.hom.app (op (n : ℕ))).hom.val.app (op U.obj)).hom).comp
        (sourceEquiv U n).toLinearMap

/-- A completed map presents all positive stages exactly when its quotient maps
commute with the supplied source and target identifications. -/
theorem isEtaleAffineStagePresentation_iff
    {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
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
      Module ((commStructureSheaf X).obj.obj (op U.obj)) (N U).obj]
    [(U : affineEtaleSite X) →
      IsScalarTower ((commStructureSheaf X).obj.obj (op U.obj))
        (AdicCompletion (idealOnEtaleChart I U.obj)
          ((commStructureSheaf X).obj.obj (op U.obj))) (N U).obj]
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
        (((G.obj).obj (op (n : ℕ))).obj.val.obj (op U.obj))) :
    IsEtaleAffineStagePresentation I alpha M N completedMap sourceEquiv targetEquiv ↔
      ∀ (U : affineEtaleSite X) (n : ℕ+),
        (targetEquiv U n).toLinearMap.comp
            (((completedMap U).restrictScalars
                ((commStructureSheaf X).obj.obj (op U.obj))).quotientMapByIdealPower
              (idealOnEtaleChart I U.obj) n) =
          (((alpha.hom.app (op (n : ℕ))).hom.val.app (op U.obj)).hom).comp
            (sourceEquiv U n).toLinearMap :=
  sorry

/-- On every affine étale chart, an explicitly supplied completed map has kernel
and cokernel annihilated by some positive power of the corresponding ideal. -/
def AffineMapsHaveKernelCokernelAnnihilation
    {S : Scheme.{u}} {X : AlgebraicSpace S} (I K : IdealSubobject X)
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
      Module ((commStructureSheaf X).obj.obj (op U.obj)) (N U).obj]
    [(U : affineEtaleSite X) →
      IsScalarTower ((commStructureSheaf X).obj.obj (op U.obj))
        (AdicCompletion (idealOnEtaleChart I U.obj)
          ((commStructureSheaf X).obj.obj (op U.obj))) (N U).obj]
    (completedMap : (U : affineEtaleSite X) →
      (M U).obj →ₗ[AdicCompletion (idealOnEtaleChart I U.obj)
          ((commStructureSheaf X).obj.obj (op U.obj))] (N U).obj) : Prop :=
  ∀ U : affineEtaleSite X,
    LinearMap.HasKernelCokernelAnnihilatedByPower (idealOnEtaleChart K U.obj)
      ((completedMap U).restrictScalars
        ((commStructureSheaf X).obj.obj (op U.obj)))

/-- Affine-chart annihilation holds exactly when each completed map has kernel
and cokernel annihilated by a positive ideal power. -/
theorem affineMapsHaveKernelCokernelAnnihilation_iff
    {S : Scheme.{u}} {X : AlgebraicSpace S} (I K : IdealSubobject X)
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
      Module ((commStructureSheaf X).obj.obj (op U.obj)) (N U).obj]
    [(U : affineEtaleSite X) →
      IsScalarTower ((commStructureSheaf X).obj.obj (op U.obj))
        (AdicCompletion (idealOnEtaleChart I U.obj)
          ((commStructureSheaf X).obj.obj (op U.obj))) (N U).obj]
    (completedMap : (U : affineEtaleSite X) →
      (M U).obj →ₗ[AdicCompletion (idealOnEtaleChart I U.obj)
          ((commStructureSheaf X).obj.obj (op U.obj))] (N U).obj) :
    AffineMapsHaveKernelCokernelAnnihilation I K M N completedMap ↔
      ∀ U : affineEtaleSite X,
        LinearMap.HasKernelCokernelAnnihilatedByPower (idealOnEtaleChart K U.obj)
          ((completedMap U).restrictScalars
            ((commStructureSheaf X).obj.obj (op U.obj))) :=
  sorry

/-- Some affine étale surjective chart has a completed map whose kernel and
cokernel are annihilated by a positive power of the corresponding ideal. -/
def ExistsCoveringAffineMapHaveKernelCokernelAnnihilation
    {S : Scheme.{u}} {X : AlgebraicSpace S} (I K : IdealSubobject X)
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
      Module ((commStructureSheaf X).obj.obj (op U.obj)) (N U).obj]
    [(U : affineEtaleSite X) →
      IsScalarTower ((commStructureSheaf X).obj.obj (op U.obj))
        (AdicCompletion (idealOnEtaleChart I U.obj)
          ((commStructureSheaf X).obj.obj (op U.obj))) (N U).obj]
    (completedMap : (U : affineEtaleSite X) →
      (M U).obj →ₗ[AdicCompletion (idealOnEtaleChart I U.obj)
          ((commStructureSheaf X).obj.obj (op U.obj))] (N U).obj) : Prop :=
  ∃ U : affineEtaleSite X,
    Surjective U.obj.hom ∧
      LinearMap.HasKernelCokernelAnnihilatedByPower (idealOnEtaleChart K U.obj)
        ((completedMap U).restrictScalars
          ((commStructureSheaf X).obj.obj (op U.obj)))

/-- Covering-chart annihilation holds exactly when a surjective affine étale
chart has a completed map with kernel and cokernel killed by a positive ideal power. -/
theorem existsCoveringAffineMapHaveKernelCokernelAnnihilation_iff
    {S : Scheme.{u}} {X : AlgebraicSpace S} (I K : IdealSubobject X)
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
      Module ((commStructureSheaf X).obj.obj (op U.obj)) (N U).obj]
    [(U : affineEtaleSite X) →
      IsScalarTower ((commStructureSheaf X).obj.obj (op U.obj))
        (AdicCompletion (idealOnEtaleChart I U.obj)
          ((commStructureSheaf X).obj.obj (op U.obj))) (N U).obj]
    (completedMap : (U : affineEtaleSite X) →
      (M U).obj →ₗ[AdicCompletion (idealOnEtaleChart I U.obj)
          ((commStructureSheaf X).obj.obj (op U.obj))] (N U).obj) :
    ExistsCoveringAffineMapHaveKernelCokernelAnnihilation I K M N completedMap ↔
      ∃ U : affineEtaleSite X,
        Surjective U.obj.hom ∧
          LinearMap.HasKernelCokernelAnnihilatedByPower (idealOnEtaleChart K U.obj)
            ((completedMap U).restrictScalars
              ((commStructureSheaf X).obj.obj (op U.obj))) :=
  sorry

/-- Uniform annihilation at every positive stage, annihilation for every affine
étale completed map, and annihilation on some affine étale surjective chart are
equivalent for a presented coherent-formal morphism. -/
theorem kernelCokernelAnnihilation_tfae
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
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
      IsEtaleAffineStagePresentation I alpha M N completedMap sourceEquiv
        targetEquiv) :
    List.TFAE [
      StagesHaveUniformKernelCokernelAnnihilation K alpha,
      AffineMapsHaveKernelCokernelAnnihilation I K M N completedMap,
      ExistsCoveringAffineMapHaveKernelCokernelAnnihilation I K M N completedMap
    ] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CoherentFormalMap
