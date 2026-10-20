/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap46.Lemma_46_3_6
public import stacks_project.Chap46.Lemma_46_3_8
public import stacks_project.Chap46.Lemma_46_3_9_Cokernels
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Cokernel
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 46.3.9 -/
@[stacks 06V1] #check (ModuleValuedFunctor.TensorAdequate.cokernelToTensorExtension :
  ∀ {A : CommRingCat.{u}} {F : ModuleValuedFunctor.bundled.{u, u} A}
    {M : ModuleCat.{u} A},
    (φ : F ⟶ (ModuleValuedFunctor.tensorExtensionFunctor A).obj M) →
      ModuleValuedFunctor.TensorAdequate F →
        ModuleValuedFunctor.TensorAdequate (ModuleValuedFunctor.pointwiseCokernel φ))
