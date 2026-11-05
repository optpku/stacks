/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.AdequateCategory
public import stacks_project.Chap46.Definition_46_3_2
public import stacks_project.Chap46.Lemma_46_3_6_TensorExtension

@[expose] public section

open CategoryTheory

universe u

/- The category of adequate module-valued functors on `Alg_A`. -/
#check (ModuleValuedFunctor.Adeq : CommRingCat.{u} → Type _)

/- Objects of the adequate category satisfy the original adequacy predicate. -/
#check (ModuleValuedFunctor.Adeq.adequate :
  ∀ {A : CommRingCat.{u}} (F : ModuleValuedFunctor.Adeq A),
    ModuleValuedFunctor.Adequate (ModuleValuedFunctor.tensorExtension A) F.obj)
