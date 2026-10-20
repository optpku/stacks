/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.LCCat.Simplicial.OpensOver
public import ReasLib.CategoryTheory.Sites.Simplicial.SliceAugmentation
public import ReasLib.Topology.Sheaves.Simplicial.Augmentation

/-! # Compatibility of qc and Zariski augmentation morphisms -/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject TopologicalSpace
open scoped Simplicial CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u

namespace LCCat

variable {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
variable (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)
variable [HasWeakSheafify (qcTopology.over X) (Type u)]
variable [HasSheafify (sliceTotalTopology qcTopology U) (Type u)]
variable [∀ P : (Opens X.obj)ᵒᵖ ⥤ Type u, (opensOver X).op.HasLeftKanExtension P]
variable [∀ P : (zariskiSite (forgetToTop.obj U))ᵒᵖ ⥤ Type u,
  (qcOpensOverTotal U).op.HasLeftKanExtension P]
variable [∀ P : (sliceTotalSite U)ᵒᵖ ⥤ Type u,
  (sliceForget U a).op.HasPointwiseRightKanExtension P]

/-- For an augmented simplicial Hausdorff locally compact space, the qc-to-Zariski
comparison morphisms commute with augmentation: the two canonical composites of
inverse-image functors are naturally isomorphic. -/
theorem qcOpensOver_inverseImage_comp :
    Nonempty
      ((augmentationMorphism (toTopCatAugmentation a))⁻¹ ⋙ (qcOpensOverTotalTopos U)⁻¹ ≅
        (opensOverQcTopos X)⁻¹ ⋙ (sliceAugmentationTopos qcTopology U a)⁻¹) := by
  sorry

end LCCat
