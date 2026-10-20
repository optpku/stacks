/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Binary products in slice categories

This leaf records the canonical binary-product instance on a slice category induced by
pullbacks in the ambient category.  It gives downstream constructions a stable typeclass
owner instead of repeating local instance pins.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

namespace Over

variable {C : Type u} [Category.{v} C]

/-- A slice category has binary products whenever the ambient category has pullbacks. -/
instance instHasBinaryProductsOfHasPullbacks [HasPullbacks C] (X : C) :
    HasBinaryProducts (Over X) := sorry

/-- A slice category has all finite products whenever the ambient category has pullbacks. -/
instance instHasFiniteProductsOfHasPullbacks [HasPullbacks C] (X : C) :
    HasFiniteProducts (Over X) := sorry

end Over

end CategoryTheory
