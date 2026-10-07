module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 basic gluing recall

Compatibility of a chosen generating family belongs to the generic
precoverage cardinality interface, not to a fixed ordinal proof script.
-/

@[expose] public section

@[stacks 0GS0] #check @CategoryTheory.Precoverage.hasCardinalLTGeneratingFamilies_iff

#check @CategoryTheory.Presieve.GeneratingFamily
