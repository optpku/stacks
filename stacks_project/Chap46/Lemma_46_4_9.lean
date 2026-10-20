/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap46.Definition_46_3_2
public import stacks_project.Chap46.Lemma_46_4_8
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace ModuleValuedFunctor

/- Lemma 46.4.9 -/
@[stacks 06ZH] #check
  (ModuleValuedFunctor.TensorLinearlyAdequate.ext_tensorExtension_subsingleton :
    {A : CommRingCat.{u}} → {L : ModuleValuedFunctor.bundled.{u, u} A} →
      ModuleValuedFunctor.TensorLinearlyAdequate L →
      (M : ModuleCat.{u} A) → (i : ℕ) → 0 < i →
      Subsingleton (@Abelian.Ext _ (ModuleValuedFunctor.bundled.{u, u} A).str
        (ModuleValuedFunctor.bundledAbelian A)
        (ModuleValuedFunctor.bundledHasExt A) L
        ((ModuleValuedFunctor.tensorExtensionFunctor A).obj M) i))

end ModuleValuedFunctor
