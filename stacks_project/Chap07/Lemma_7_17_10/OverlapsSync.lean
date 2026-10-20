/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import ReasLib.SetTheory.Ordinal.Cofinality
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 overlap-synchronization recall

Synchronization of fewer than `β.cof` many stagewise facts is the neutral
cofinality API on ordinals, not a bespoke dependent witness package.
-/

@[expose] public section

@[stacks 0GS0] #check @Ordinal.ToType.exists_upperBound_of_lift_mk_lt_cof

#check @CategoryTheory.Precoverage.FilteredColimitSections.isIso_of_ordinal
