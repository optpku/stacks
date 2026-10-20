/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 fixed-overlap recall

The temporary fixed-target overlap witness was tailored to one proof route and
is not retained as reusable data.  The cardinal cover interface retains the
stable presentation data needed downstream.
-/

@[expose] public section

@[stacks 0GS0] #check @CategoryTheory.Presieve.GeneratingFamily.ofUncurry

#check @CategoryTheory.Precoverage.hasCardinalLTCoveringPresieves
