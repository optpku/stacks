/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.FilteredColimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 46.3.3: an adequate module-valued functor preserves filtered colimits after
forgetting to additive groups. Here `underline` abstracts the functors `B ↦ M ⊗[A] B`
appearing in an adequate presentation. -/
@[stacks 06UU]
#check
  (Adequate.preservesFilteredColimits :
    ∀ {A : CommRingCat.{u}}
      {underline : ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u})}
      {F : Under A ⥤ AddCommGrpCat.{u}}
      (hF : Adequate A underline F)
      [∀ M, PreservesFilteredColimits (underline.obj M)],
      PreservesFilteredColimits F)
