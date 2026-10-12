/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import ReasLib.SetTheory.Ordinal.Cofinality
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 stage-synchronization recall

Later-stage transport is an implementation of ordinal cofinality; its stable
downstream surface is the common-upper-bound and ordinal comparison APIs.
-/

@[expose] public section

@[stacks 0GS0] #check @Ordinal.ToType.exists_upperBound_of_lift_mk_lt_cof

#check @CategoryTheory.Sites.FilteredColimitSections.isIso_of_ordinal
