/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.FilteredColimits
import StacksCheckRecall

@[expose] public section

/- The former Chapter 21 helper was exactly the categorical form of the filtered-colimit
sections theorem already owned by ReasLib. This historical path remains a compatibility recall
and introduces no second declaration. -/
#check @CategoryTheory.Sites.FilteredColimitSections.isIso_ofCofinalRefinement
