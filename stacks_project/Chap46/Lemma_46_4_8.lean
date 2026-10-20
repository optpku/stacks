/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Ext
public import stacks_project.Chap46.Lemma_46_3_6_TensorExtension
public import stacks_project.Chap46.Lemma_46_4_8_Abelian
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace ModuleValuedFunctor

/- Lemma 46.4.8 -/
@[stacks 06ZG] #check (ModuleValuedFunctor.ext_tensorExtension_subsingleton :
  (A : CommRingCat.{u}) → (M P : ModuleCat.{u} A) →
      [Module.FinitePresentation A P] → (i : ℕ) → 0 < i →
      Subsingleton (@Abelian.Ext _ (ModuleValuedFunctor.bundled.{u, u} A).str
        (ModuleValuedFunctor.bundledAbelian A) (ModuleValuedFunctor.bundledHasExt A)
        ((ModuleValuedFunctor.tensorExtensionFunctor A).obj P)
        ((ModuleValuedFunctor.tensorExtensionFunctor A).obj M) i))

end ModuleValuedFunctor
