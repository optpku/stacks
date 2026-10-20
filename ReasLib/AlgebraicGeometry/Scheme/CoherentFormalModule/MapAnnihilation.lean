/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Category
public import ReasLib.LinearAlgebra.QuotientByIdeal
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Annihilation conditions for maps of coherent formal modules

This file relates the finite stages of a morphism of coherent formal modules to explicitly
supplied maps between finite modules over affine adic completions. It also records the global,
affine-local, and finite-cover forms of kernel-and-cokernel annihilation.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalMap

/-- Explicit affine completed modules and their maps present the stages of a coherent-formal
morphism when the quotient maps commute with the supplied identifications at every positive
stage. -/
def IsAffineStagePresentation
    {X : Scheme.{u}} (I : X.IdealSheafData)
    {F G : CoherentFormalModules X I} (alpha : F ⟶ G)
    (M N : (U : X.affineOpens) →
      FGModuleCat (AdicCompletion (I.ideal U) Γ(X, U.1)))
    [(U : X.affineOpens) → Module Γ(X, U.1) (M U).obj]
    [(U : X.affineOpens) →
      IsScalarTower Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)) (M U).obj]
    [(U : X.affineOpens) → Module Γ(X, U.1) (N U).obj]
    [(U : X.affineOpens) →
      IsScalarTower Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)) (N U).obj]
    (completedMap : (U : X.affineOpens) →
      (M U).obj →ₗ[AdicCompletion (I.ideal U) Γ(X, U.1)] (N U).obj)
    (sourceEquiv : (U : X.affineOpens) → (n : ℕ+) →
      ((M U).obj ⧸
          I.ideal U ^ (n : ℕ) • (⊤ : Submodule Γ(X, U.1) (M U).obj)) ≃ₗ[Γ(X, U.1)]
        (((F.obj).obj (op (n : ℕ))).obj.val.obj (op U.1)))
    (targetEquiv : (U : X.affineOpens) → (n : ℕ+) →
      ((N U).obj ⧸
          I.ideal U ^ (n : ℕ) • (⊤ : Submodule Γ(X, U.1) (N U).obj)) ≃ₗ[Γ(X, U.1)]
        (((G.obj).obj (op (n : ℕ))).obj.val.obj (op U.1))) : Prop :=
  ∀ (U : X.affineOpens) (n : ℕ+),
    (targetEquiv U n).toLinearMap.comp
        (((completedMap U).restrictScalars Γ(X, U.1)).quotientMapByIdealPower
          (I.ideal U) n) =
      (((alpha.hom.app (op (n : ℕ))).hom.val.app (op U.1)).hom).comp
        (sourceEquiv U n).toLinearMap

/-- Unfold the commuting condition defining an affine presentation of all positive stages. -/
theorem isAffineStagePresentation_iff
    {X : Scheme.{u}} (I : X.IdealSheafData)
    {F G : CoherentFormalModules X I} (alpha : F ⟶ G)
    (M N : (U : X.affineOpens) →
      FGModuleCat (AdicCompletion (I.ideal U) Γ(X, U.1)))
    [(U : X.affineOpens) → Module Γ(X, U.1) (M U).obj]
    [(U : X.affineOpens) →
      IsScalarTower Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)) (M U).obj]
    [(U : X.affineOpens) → Module Γ(X, U.1) (N U).obj]
    [(U : X.affineOpens) →
      IsScalarTower Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)) (N U).obj]
    (completedMap : (U : X.affineOpens) →
      (M U).obj →ₗ[AdicCompletion (I.ideal U) Γ(X, U.1)] (N U).obj)
    (sourceEquiv : (U : X.affineOpens) → (n : ℕ+) →
      ((M U).obj ⧸
          I.ideal U ^ (n : ℕ) • (⊤ : Submodule Γ(X, U.1) (M U).obj)) ≃ₗ[Γ(X, U.1)]
        (((F.obj).obj (op (n : ℕ))).obj.val.obj (op U.1)))
    (targetEquiv : (U : X.affineOpens) → (n : ℕ+) →
      ((N U).obj ⧸
          I.ideal U ^ (n : ℕ) • (⊤ : Submodule Γ(X, U.1) (N U).obj)) ≃ₗ[Γ(X, U.1)]
        (((G.obj).obj (op (n : ℕ))).obj.val.obj (op U.1))) :
    IsAffineStagePresentation I alpha M N completedMap sourceEquiv targetEquiv ↔
      ∀ (U : X.affineOpens) (n : ℕ+),
        (targetEquiv U n).toLinearMap.comp
            (((completedMap U).restrictScalars Γ(X, U.1)).quotientMapByIdealPower
              (I.ideal U) n) =
          (((alpha.hom.app (op (n : ℕ))).hom.val.app (op U.1)).hom).comp
            (sourceEquiv U n).toLinearMap :=
  Iff.rfl

/-- One positive power of an ideal sheaf annihilates the kernels and cokernels of every positive
stage of a coherent-formal morphism on every affine open. -/
def StagesHaveUniformKernelCokernelAnnihilation
    {X : Scheme.{u}} {I : X.IdealSheafData} (K : X.IdealSheafData)
    {F G : CoherentFormalModules X I} (alpha : F ⟶ G) : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧ ∀ (U : X.affineOpens) (n : ℕ+),
    ∀ a ∈ K.ideal U ^ t,
      (∀ x,
        ((alpha.hom.app (op (n : ℕ))).hom.val.app (op U.1)).hom x = 0 →
          a • x = 0) ∧
        ∀ y : (((G.obj).obj (op (n : ℕ))).obj.val.obj (op U.1)), a • y ∈
          (((alpha.hom.app (op (n : ℕ))).hom.val.app (op U.1)).hom).range

/-- Unfold uniform kernel-and-cokernel annihilation across all positive stages and affine opens. -/
theorem stagesHaveUniformKernelCokernelAnnihilation_iff
    {X : Scheme.{u}} {I : X.IdealSheafData} (K : X.IdealSheafData)
    {F G : CoherentFormalModules X I} (alpha : F ⟶ G) :
    StagesHaveUniformKernelCokernelAnnihilation K alpha ↔
      ∃ t : ℕ, 1 ≤ t ∧ ∀ (U : X.affineOpens) (n : ℕ+),
        ∀ a ∈ K.ideal U ^ t,
          (∀ x,
            ((alpha.hom.app (op (n : ℕ))).hom.val.app (op U.1)).hom x = 0 →
              a • x = 0) ∧
            ∀ y : (((G.obj).obj (op (n : ℕ))).obj.val.obj (op U.1)), a • y ∈
              (((alpha.hom.app (op (n : ℕ))).hom.val.app (op U.1)).hom).range :=
  Iff.rfl

/-- On every affine open, an explicitly supplied completed map has kernel and cokernel
annihilated by some positive power of the corresponding ideal. -/
def AffineMapsHaveKernelCokernelAnnihilation
    {X : Scheme.{u}} (I K : X.IdealSheafData)
    (M N : (U : X.affineOpens) →
      FGModuleCat (AdicCompletion (I.ideal U) Γ(X, U.1)))
    [(U : X.affineOpens) → Module Γ(X, U.1) (M U).obj]
    [(U : X.affineOpens) →
      IsScalarTower Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)) (M U).obj]
    [(U : X.affineOpens) → Module Γ(X, U.1) (N U).obj]
    [(U : X.affineOpens) →
      IsScalarTower Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)) (N U).obj]
    (completedMap : (U : X.affineOpens) →
      (M U).obj →ₗ[AdicCompletion (I.ideal U) Γ(X, U.1)] (N U).obj) : Prop :=
  ∀ U : X.affineOpens,
    LinearMap.HasKernelCokernelAnnihilatedByPower (K.ideal U)
      ((completedMap U).restrictScalars Γ(X, U.1))

/-- Unfold affine-local kernel-and-cokernel annihilation for the completed maps. -/
theorem affineMapsHaveKernelCokernelAnnihilation_iff
    {X : Scheme.{u}} (I K : X.IdealSheafData)
    (M N : (U : X.affineOpens) →
      FGModuleCat (AdicCompletion (I.ideal U) Γ(X, U.1)))
    [(U : X.affineOpens) → Module Γ(X, U.1) (M U).obj]
    [(U : X.affineOpens) →
      IsScalarTower Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)) (M U).obj]
    [(U : X.affineOpens) → Module Γ(X, U.1) (N U).obj]
    [(U : X.affineOpens) →
      IsScalarTower Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)) (N U).obj]
    (completedMap : (U : X.affineOpens) →
      (M U).obj →ₗ[AdicCompletion (I.ideal U) Γ(X, U.1)] (N U).obj) :
    AffineMapsHaveKernelCokernelAnnihilation I K M N completedMap ↔
      ∀ U : X.affineOpens,
        LinearMap.HasKernelCokernelAnnihilatedByPower (K.ideal U)
          ((completedMap U).restrictScalars Γ(X, U.1)) :=
  Iff.rfl

/-- A finite affine open cover has completed maps whose kernels and cokernels are each
annihilated by a positive power of the corresponding ideal. -/
def AffineMapsHaveKernelCokernelAnnihilationOnFiniteCover
    {X : Scheme.{u}} (I K : X.IdealSheafData)
    (M N : (U : X.affineOpens) →
      FGModuleCat (AdicCompletion (I.ideal U) Γ(X, U.1)))
    [(U : X.affineOpens) → Module Γ(X, U.1) (M U).obj]
    [(U : X.affineOpens) →
      IsScalarTower Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)) (M U).obj]
    [(U : X.affineOpens) → Module Γ(X, U.1) (N U).obj]
    [(U : X.affineOpens) →
      IsScalarTower Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)) (N U).obj]
    (completedMap : (U : X.affineOpens) →
      (M U).obj →ₗ[AdicCompletion (I.ideal U) Γ(X, U.1)] (N U).obj) : Prop :=
  ∃ s : Finset X.affineOpens,
    (∀ x : X, ∃ U ∈ s, x ∈ (U : Set X)) ∧
      ∀ U ∈ s, LinearMap.HasKernelCokernelAnnihilatedByPower (K.ideal U)
        ((completedMap U).restrictScalars Γ(X, U.1))

/-- Unfold kernel-and-cokernel annihilation on a finite affine open cover. -/
theorem affineMapsHaveKernelCokernelAnnihilationOnFiniteCover_iff
    {X : Scheme.{u}} (I K : X.IdealSheafData)
    (M N : (U : X.affineOpens) →
      FGModuleCat (AdicCompletion (I.ideal U) Γ(X, U.1)))
    [(U : X.affineOpens) → Module Γ(X, U.1) (M U).obj]
    [(U : X.affineOpens) →
      IsScalarTower Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)) (M U).obj]
    [(U : X.affineOpens) → Module Γ(X, U.1) (N U).obj]
    [(U : X.affineOpens) →
      IsScalarTower Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)) (N U).obj]
    (completedMap : (U : X.affineOpens) →
      (M U).obj →ₗ[AdicCompletion (I.ideal U) Γ(X, U.1)] (N U).obj) :
    AffineMapsHaveKernelCokernelAnnihilationOnFiniteCover I K M N completedMap ↔
      ∃ s : Finset X.affineOpens,
        (∀ x : X, ∃ U ∈ s, x ∈ (U : Set X)) ∧
          ∀ U ∈ s, LinearMap.HasKernelCokernelAnnihilatedByPower (K.ideal U)
            ((completedMap U).restrictScalars Γ(X, U.1)) :=
  Iff.rfl

/-- Uniform annihilation at every positive stage, annihilation for every affine completed map,
and annihilation on a finite affine cover are equivalent for a presented coherent-formal
morphism. -/
@[stacks 0888]
theorem kernelCokernelAnnihilation_tfae
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    {F G : CoherentFormalModules X I} (alpha : F ⟶ G)
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
    (presentation : IsAffineStagePresentation I alpha M N completedMap sourceEquiv targetEquiv) :
    List.TFAE [
      StagesHaveUniformKernelCokernelAnnihilation K alpha,
      AffineMapsHaveKernelCokernelAnnihilation I K M N completedMap,
      AffineMapsHaveKernelCokernelAnnihilationOnFiniteCover I K M N completedMap
    ] := sorry

end AlgebraicGeometry.Scheme.CoherentFormalMap
