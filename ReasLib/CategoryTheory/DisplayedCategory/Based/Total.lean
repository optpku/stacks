/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.Total
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory

/-!
# Based projection of a displayed total category

The ordinary total category is independent of based-category infrastructure.  This leaf adds the
optional view of its base projection as a `BasedCategory`, while preserving the canonical
`DisplayedCategory.Total.toBased` name used by downstream code.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

namespace DisplayedCategory.Total

/-- View the total category of a displayed category as a category over its base. -/
def toBased (D : DisplayedCategory C) : BasedCategory C :=
  BasedCategory.ofFunctor (forget D)

/-- The projection stored by `toBased` is the canonical total-category projection. -/
@[simp]
theorem toBased_p (D : DisplayedCategory C) :
    (toBased D).p = forget D := sorry

end DisplayedCategory.Total

end CategoryTheory
