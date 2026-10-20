/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Pro.Sequential.Homology.Value
import StacksCheckRecall

@[expose] public section

/- Lemma 13.42.3: uniformly bounded sequential derived towers have a pro-value whose homology
gives the degreewise values; in particular the tower is essentially constant. -/
@[stacks 0G3B] #check @CategoryTheory.DerivedCategory.Pro.Sequential.Homology.existsValue

#check @CategoryTheory.DerivedCategory.Pro.Sequential.Homology.essentiallyConstant
