/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.FlatBaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits RingHom

universe u

/- Lemma 46.3.5: tensor adequacy of a module-valued functor implies that its canonical
extension-of-scalars comparison is an isomorphism along every flat algebra morphism. -/
@[stacks 06UW] #check (ModuleValuedFunctor.TensorAdequate.hasFlatBaseChange :
  ∀ {A : CommRingCat.{u}} {F : ModuleValuedFunctor.bundled.{u, u} A},
    ModuleValuedFunctor.TensorAdequate F → ModuleValuedFunctor.HasFlatBaseChange F)
