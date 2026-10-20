/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.BaseChangeExact
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {A A' : CommRingCat.{u}}

namespace ModuleValuedFunctor

/- Lemma 46.3.20: let `f : A ⟶ A'` be a ring map and let `F` be a module-valued
functor on `A`-algebras. If its restriction to `A'`-algebras is adequate and the
base-change sequence is objectwise injective and exact, then `F` is adequate. -/
@[stacks 06VH] #check
  (ModuleValuedFunctor.Adequate.of_baseChange_exact :
    ∀ {A A' : CommRingCat.{u}} (f : A ⟶ A')
      (F : ModuleValuedFunctor.bundled.{u, u} A),
      ModuleValuedFunctor.TensorAdequate
          ((ModuleValuedFunctor.restrictAlong f).obj F) →
        (∀ B, Function.Injective
          ((CategoryTheory.Under.baseChangeUnit f F.toFunctor).app B)) →
        (∀ B, Function.Exact
          ((CategoryTheory.Under.baseChangeUnit f F.toFunctor).app B)
          ((CategoryTheory.Under.baseChangeDifferential f F.toFunctor).app B)) →
        ModuleValuedFunctor.TensorAdequate F)

end ModuleValuedFunctor
