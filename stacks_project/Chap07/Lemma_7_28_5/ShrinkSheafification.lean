/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.ShrinkType
public import ReasLib.CategoryTheory.Sites.TypeSheafification
public import StacksCheckRecall.CommandCrossRef

/-!
# Shrink sheafification recall

The canonical owner for `Shrink` carriers and their sheafification interface
is `ReasLib.CategoryTheory.Sites.ShrinkType`; this legacy leaf adds no local
compatibility wrappers.
-/

@[expose] public section

@[stacks 0D5R "shrink sheafification"] #check @CategoryTheory.Sites.typeShrinkMap
#check @CategoryTheory.Sites.shrinkForget
#check @CategoryTheory.Sites.isLocallyInjective_whisker_shrinkForget
#check @CategoryTheory.Sites.isLocallySurjective_whisker_shrinkForget
#check @CategoryTheory.Sites.locallyInjective_of_shrink
#check @CategoryTheory.Sites.shrinkForget_preservesSheafification_of_WEqualsLocallyBijective
