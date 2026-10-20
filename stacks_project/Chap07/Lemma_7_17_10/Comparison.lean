/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import ReasLib.CategoryTheory.Sites.Sheaf.Colimit
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 comparison recall

The sheafified presheaf-colimit comparison is a reusable filtered-colimit
API.  The prior local proof of sheafness and separatedness is subsumed by the
ordinal comparison theorem.
-/

@[expose] public section

@[stacks 0GS0] #check @CategoryTheory.Precoverage.FilteredColimitSections.isIso_of_ordinal

#check @CategoryTheory.Precoverage.FilteredColimitSections.bijective_of_ordinal
#check @CategoryTheory.Sheaf.sheafifyColimitIso
