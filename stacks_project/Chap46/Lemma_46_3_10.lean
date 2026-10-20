/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Cokernel
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 46.3.10 -/
@[stacks 06V2] #check (ModuleValuedFunctor.Adequate.cokernel :
  ∀ {A : CommRingCat.{u}} {F G : ModuleValuedFunctor.bundled.{u, u} A},
    (φ : F ⟶ G) →
      ModuleValuedFunctor.TensorAdequate F →
        ModuleValuedFunctor.TensorAdequate G →
          ModuleValuedFunctor.TensorAdequate (ModuleValuedFunctor.pointwiseCokernel φ))
