/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 local-pullback recall

The old chosen local-pullback structure encoded one proof's implementation
choices.  It is deliberately replaced by the presentation-independent ordinal
comparison API.
-/

@[expose] public section

@[stacks 0GS0] #check @CategoryTheory.Precoverage.FilteredColimitSections.isIso_of_ordinal

#check @CategoryTheory.Presieve.GeneratingFamily.ofUncurry
