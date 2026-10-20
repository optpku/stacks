/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.ChangeOfRings
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-! Lemma 21.39.6 (08Q8) is recalled from the reusable derived-colimit/change-of-rings owner.
The constant-ring sheaf statement is represented by its canonical module-presheaf presentation.
-/

@[stacks 08Q8]
#check @CategoryTheory.DerivedColimit.ChangeOfRings.lowerShriek_isomorphic
