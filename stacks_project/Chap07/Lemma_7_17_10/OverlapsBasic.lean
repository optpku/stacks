module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 basic-overlap recall

Basic overlap synchronization is absorbed into the cardinally bounded
filtered-colimit comparison API.
-/

@[expose] public section

@[stacks 0GS0] #check @CategoryTheory.Precoverage.hasCardinalLTCoveringPresieves

#check @CategoryTheory.Precoverage.FilteredColimitSections.bijective_of_ordinal
