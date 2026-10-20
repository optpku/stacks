/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 overlap recall

The former overlap descent tree carried no independent public mathematical
statement.  Its result is represented by the reusable ordinal comparison.
-/

@[expose] public section

@[stacks 0GS0] #check @CategoryTheory.Sites.FilteredColimitSections.isIso_of_ordinal

#check @CategoryTheory.Precoverage.FilteredColimitSections.isIso_of_ordinal
