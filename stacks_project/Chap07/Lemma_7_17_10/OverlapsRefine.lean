module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 overlap-refinement recall

Branchwise refinements are an internal derivation of the cardinal cover
condition, which is exposed through `hasCardinalLTCoveringPresieves`.
-/

@[expose] public section

@[stacks 0GS0] #check @CategoryTheory.Precoverage.hasCardinalLTCoveringPresieves

#check @CategoryTheory.Precoverage.hasCardinalLTGeneratingFamilies_iff
