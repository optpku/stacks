/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 overlap-geometry recall

The geometry of iterated local pullbacks is used internally by one proof, but
does not define a stable source-independent abstraction beyond cover descent.
-/

@[expose] public section

@[stacks 0GS0] #check @CategoryTheory.Precoverage.FilteredColimitSections.isIso_of_ordinal

#check @CategoryTheory.Presieve.ofArrows_uncurry_eq
