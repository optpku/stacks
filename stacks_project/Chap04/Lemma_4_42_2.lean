/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.PseudoPullback.Slice
import StacksCheckRecall

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
variable (F : X ⥤ᵇ Y) {U : C}
variable (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ Y)

/- Lemma 4.42.2: for morphisms `F : X ⥤ᵇ Y` and `G : C/U ⥤ᵇ Y` of categories fibred
in groupoids over `C`, `PseudoPullback.fst G F` is a category fibred in groupoids over `C/U`.
The reusable source-shaped owner is
`BasedCategory.PseudoPullback.fstGroupoids F G`. -/
@[stacks 02Y6]
#check (fun [Functor.IsFibered.InGroupoids X.p]
    [Functor.IsFibered.InGroupoids Y.p] ↦
  BasedCategory.PseudoPullback.fstGroupoids F G :
    ∀ [Functor.IsFibered.InGroupoids X.p]
        [Functor.IsFibered.InGroupoids Y.p],
      FiberedCategoryOver.Groupoids (Over U))

end CategoryTheory
