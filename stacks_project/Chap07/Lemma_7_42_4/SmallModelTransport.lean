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
# Small-model transport recall

The former proof-infrastructure module duplicated universe-shrinking and
type-valued sheafification APIs.  Their canonical reusable owners are now in
ReasLib, so this legacy leaf deliberately exposes no competing Chapter API.
-/

@[expose] public section

@[stacks 04B8 "small-model transport"] #check @CategoryTheory.Sites.shrinkForget
#check @CategoryTheory.Sites.shrinkForget_preservesSheafification_of_WEqualsLocallyBijective
#check @CategoryTheory.GrothendieckTopology.toSheafify_isLocallySurjective_type
#check @CategoryTheory.GrothendieckTopology.type_WEqualsLocallyBijective_of_toSheafify_isLocallyInjective
