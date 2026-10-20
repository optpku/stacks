/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.LCCat.Simplicial.Comparison
import StacksCheckRecall

/-!
# Lemma 85.25.1

Let `U` be a simplicial object of `LCCat` and let `a : U ⟶ X` be an
augmentation. There is a commutative square of morphisms of topoi
`Sh((LC_qc / U)_total) ⟶ Sh(U_Zar)` over `Sh(LC_qc / X) ⟶ Sh(X)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject TopologicalSpace LCCat
open scoped Simplicial CategoryTheory.MorphismOfTopoiIn

universe u

variable {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
variable (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)
variable [HasWeakSheafify (qcTopology.over X) (Type u)]
variable [HasSheafify (sliceTotalTopology qcTopology U) (Type u)]
variable [∀ P : (Opens X.obj)ᵒᵖ ⥤ Type u, (opensOver X).op.HasLeftKanExtension P]
variable [∀ P : (zariskiSite (forgetToTop.obj U))ᵒᵖ ⥤ Type u,
  (qcOpensOverTotal U).op.HasLeftKanExtension P]
variable [∀ P : (sliceTotalSite U)ᵒᵖ ⥤ Type u,
  (sliceForget U a).op.HasPointwiseRightKanExtension P]

/- Lemma 85.25.1
Let `U` be a simplicial object of `LCCat` and let `a : U ⟶ X` be an
augmentation. There is a commutative square of morphisms of topoi
`Sh((LC_qc / U)_total) ⟶ Sh(U_Zar)` over `Sh(LC_qc / X) ⟶ Sh(X)`, whose left vertical
arrow `a_qc` is the Section 85.21 slice augmentation `sliceAugmentationTopos qcTopology`,
whose right vertical arrow `a` is the Lemma 85.2.8 Zariski augmentation
`augmentationMorphism (toTopCatAugmentation a)`, and whose horizontal arrows are
`h = qcOpensOverTotalTopos` presented by `V ↦ V / U_n` and
`h₋₁ = opensOverQcTopos` presented by `V ↦ V / X`. -/
@[stacks 0DAF] #check (LCCat.qcOpensOver_inverseImage_comp a :
    Nonempty
      ((augmentationMorphism (toTopCatAugmentation a))⁻¹ ⋙ (qcOpensOverTotalTopos U)⁻¹ ≅
        (opensOverQcTopos X)⁻¹ ⋙ (sliceAugmentationTopos qcTopology U a)⁻¹))
