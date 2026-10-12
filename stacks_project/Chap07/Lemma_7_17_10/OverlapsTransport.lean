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
# Lemma 7.17.10 overlap-transport recall

Transporting local equalities to a common ordinal stage is covered by the
generic cofinality owner rather than a chapter-specific restriction lemma.
-/

@[expose] public section

@[stacks 0GS0] #check @Ordinal.ToType.exists_upperBound_of_lift_mk_lt_cof

#check @CategoryTheory.Precoverage.FilteredColimitSections.isIso_of_ordinal
