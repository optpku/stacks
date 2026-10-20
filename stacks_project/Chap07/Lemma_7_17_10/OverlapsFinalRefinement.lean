module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 refined-overlap recall

Refined common-source witnesses are proof-local.  They are intentionally not
published as a dependent-index API; use the canonical ordinal theorem.
-/

@[expose] public section

@[stacks 0GS0] #check @CategoryTheory.Precoverage.FilteredColimitSections.isIso_of_ordinal

#check @CategoryTheory.Precoverage.hasCardinalLTGeneratingFamilies_iff
