/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 final-overlap recall

The fixed-target overlap normalization was only an intermediate proof form;
the library surface remains the ordinal section comparison.
-/

@[expose] public section

@[stacks 0GS0] #check @CategoryTheory.Sites.FilteredColimitSections.isIso_of_ordinal

#check @CategoryTheory.Presieve.ofArrows_uncurry_eq
