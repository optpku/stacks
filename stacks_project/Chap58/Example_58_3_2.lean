/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Action.Finite.Forget
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped FintypeCatDiscrete

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- Example 58.3.2: finite discrete continuous `G`-actions and their
underlying-set functor to `Type u`. -/
@[stacks 0BMS] #check
  (CategoryTheory.DiscreteContAction.forgetFinite G :
    DiscreteContAction FintypeCat.{u} G ⥤ Type u)
