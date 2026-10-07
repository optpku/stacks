module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 target-synchronization recall

Fixed-target equality descent is proof-local to this construction.  The
canonical reusable conclusion is the precoverage ordinal comparison.
-/

@[expose] public section

@[stacks 0GS0] #check @CategoryTheory.Precoverage.FilteredColimitSections.isIso_of_ordinal

#check @CategoryTheory.Precoverage.FilteredColimitSections.bijective_of_ordinal
