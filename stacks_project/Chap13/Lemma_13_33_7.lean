/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Colimit.Sequential
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.33.7

Termwise sequential colimits in derived categories are owned by
`DerivedCategory.SequentialColimit`.  The shared leaf uses the opt-in
`CountableFromSequential` scope to obtain countable coproducts without adding
a global typeclass-search cycle.
-/

/- Lemma 13.33.7: under exact sequential colimits, the derived image of the
termwise colimit is a homotopy colimit of the derived sequence. -/
@[stacks 0949] #check @CategoryTheory.DerivedCategory.SequentialColimit.isOf

/- Companion check: the reusable telescope presentation is concrete data. -/
@[stacks 0949]
#check @CategoryTheory.DerivedCategory.SequentialColimit.presentation

/- Companion checks: its cone and connecting maps are separately reusable. -/
@[stacks 0949] #check @CategoryTheory.DerivedCategory.SequentialColimit.toCocone

@[stacks 0949]
#check @CategoryTheory.DerivedCategory.SequentialColimit.connecting

/- Companion check: the presentation computes on every colimit leg. -/
@[stacks 0949]
#check @CategoryTheory.DerivedCategory.SequentialColimit.presentation.ι
