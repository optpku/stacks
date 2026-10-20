/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Action.Continuous
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- Definition 58.2.1 -/
@[stacks 04JJ] #check (DiscreteContAction.ofAction :
  (action : Action TopCat.{u} G) → action.IsContinuous →
    DiscreteTopology action.V → DiscreteContAction TopCat.{u} G)
#check (DiscreteContAction TopCat.{u} G : Type (u + 1))
