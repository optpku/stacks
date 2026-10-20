/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Closure

@[expose] public section

universe uC uS vC vS

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]
variable (p : S ⥤ C) [Functor.IsFibered.InGroupoids p]

/- Lemma 4.39.7: for a category fibred in groupoids, the canonical functor forgetting the
automorphism from absolute inertia is an equivalence exactly when the original projection is
fibred in setoids. -/
@[stacks 042J]
#check (RelativeInertia.forget.isEquivalence_iff_inSetoids p :
  (RelativeInertia.forget p).IsEquivalence ↔
    Functor.IsFibered.InSetoids p)

/- The based-category form retains the equivalence over the common base. -/
#check fun (X : BasedCategory.{vS, uS} C)
    [Functor.IsFibered.InGroupoids X.p] ↦
  BasedCategory.Inertia.forget.isEquivalence_iff_inSetoids X

end CategoryTheory
