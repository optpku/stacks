/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 sigma-gluing recall

The sigma-indexed cover construction was used only to prove the ordinal
comparison.  Downstream code should use the cardinal-cover and comparison
owners directly.
-/

@[expose] public section

@[stacks 0GS0] #check @CategoryTheory.Precoverage.hasCardinalLTCoveringPresieves

#check @CategoryTheory.Precoverage.FilteredColimitSections.isIso_of_ordinal
