/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.IntMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Symmetric
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site

/-!
# Symmetric monoidal cochain complexes of modules on a ringed space

This is the direct import boundary assembling the canonical ringed-site tensor, its closed and
preadditive properties, integer totalization, and the Koszul symmetry. The cochain-level closed
structure is registered here as the single canonical ringed-space instance; no parallel
ringed-space-specific tensor is introduced.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})

/-- The total tensor product of integer-graded modules on a ringed space exists. -/
theorem modulesIntGradedHasTensor :
    ∀ G₁ G₂ : GradedObject ℤ (Modules X), GradedObject.HasTensor G₁ G₂ :=
  fun G₁ G₂ ↦ SheafOfModules.RingedSite.IntGraded.hasTensor G₁ G₂

/-- Left-associated integer-graded tensor totalization on a ringed space is coherent. -/
theorem modulesIntGradedHasGoodTensor₁₂Tensor :
    ∀ G₁ G₂ G₃ : GradedObject ℤ (Modules X),
      GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃ :=
  fun G₁ G₂ G₃ ↦
    SheafOfModules.RingedSite.IntGraded.hasGoodTensor₁₂Tensor G₁ G₂ G₃

/-- Right-associated integer-graded tensor totalization on a ringed space is coherent. -/
theorem modulesIntGradedHasGoodTensorTensor₂₃ :
    ∀ G₁ G₂ G₃ : GradedObject ℤ (Modules X),
      GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃ :=
  fun G₁ G₂ G₃ ↦
    SheafOfModules.RingedSite.IntGraded.hasGoodTensorTensor₂₃ G₁ G₂ G₃

/-- Fourfold integer-graded tensor totalization on a ringed space is coherent. -/
theorem modulesIntGradedHasTensor₄ObjExt :
    ∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (Modules X),
      GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄ :=
  fun G₁ G₂ G₃ G₄ ↦
    SheafOfModules.RingedSite.IntGraded.hasTensor₄ObjExt G₁ G₂ G₃ G₄

/- The module-sheaf conditions assembled above supply the generic closed cochain construction.
Register it once at the ringed-space boundary so internal-Hom statements can rely on inference. -/
/-- The canonical closed structure on integer cochain complexes of modules on a ringed space. -/
@[stacks 0FRS "closed cochain complexes of ringed-space modules"]
noncomputable instance cochainComplexMonoidalClosed :
    MonoidalClosed (CochainComplex (Modules X) ℤ) :=
  CategoryTheory.CochainComplex.InternalHom.monoidalClosed


end AlgebraicGeometry.RingedSpace
