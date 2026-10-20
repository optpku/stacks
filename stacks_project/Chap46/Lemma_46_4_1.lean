/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap46.Lemma_46_4_1_Coreflection
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Coreflection
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace ModuleValuedFunctor.Adequate

/- Lemma 46.4.1: every module-valued functor `F` on `Alg_A` admits a morphism
`q : Q.obj ⟶ F` from an adequate functor such that postcomposition with `q`
is a bijection on morphisms from every adequate functor. -/
@[stacks 06Z6] #check
  (ModuleValuedFunctor.TensorAdequate.exists_coreflection :
    ∀ (A : CommRingCat.{u}) (F : ModuleValuedFunctor.bundled.{u, u} A),
      ∃ (Q : ModuleValuedFunctor.TensorAdeq A) (q : Q.obj ⟶ F),
        ∀ G : ModuleValuedFunctor.TensorAdeq A,
          Function.Bijective (fun f : G.obj ⟶ Q.obj ↦ f ≫ q))

end ModuleValuedFunctor.Adequate
