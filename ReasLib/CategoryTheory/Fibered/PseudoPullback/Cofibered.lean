/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Relative products of categories cofibered in groupoids

The relative product of two categories cofibered in groupoids is again
cofibered in groupoids over their common base.
-/

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory.BasedCategory.PseudoPullback

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- The projection of the relative product of two categories cofibered in
groupoids is cofibered in groupoids. -/
instance instIsCofiberedInGroupoidsRelativeProduct
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op] :
    Functor.IsFibered.InGroupoids
      (BasedCategory.PseudoPullback (BasedCategory.toBase X) (BasedCategory.toBase Y)).p.op :=
  sorry

end CategoryTheory.BasedCategory.PseudoPullback
