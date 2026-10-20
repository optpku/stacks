/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Derived.Limit
import StacksCheckRecall

@[expose] public section

/- Lemma 21.23.1 (0941): for an inverse-system object of the derived category of abelian sheaves,
the total right derived inverse limit is a derived limit of the stagewise evaluation tower. -/
@[stacks 0941]
#check @CategoryTheory.AbelianSheaf.DerivedLimit.isDerivedLimit_of_tower

#check @CategoryTheory.AbelianSheaf.Sequential.hasDerivedCategory
#check @CategoryTheory.DerivedLimit.Stage.tower
#check @CategoryTheory.DerivedLimit.functor
