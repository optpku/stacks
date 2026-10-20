/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import ReasLib.CategoryTheory.Limits.Over.Products

/-!
# Finite limits in slice categories

A category with pullbacks need not itself have a terminal object.  Every slice does, however,
and its finite products are the ambient pullbacks.  This leaf packages the resulting finite-limit
instance so consumers do not have to rebuild slice limit data locally.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

namespace Over

variable {C : Type u} [Category.{v} C]

/-- A slice category has all finite limits whenever the ambient category has pullbacks. -/
instance instHasFiniteLimitsOfHasPullbacks [HasPullbacks C] (X : C) :
    HasFiniteLimits (Over X) := sorry

end Over

end CategoryTheory
