module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import ReasLib.SetTheory.Ordinal.Cofinality
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 family-synchronization recall

The generic common-upper-bound theorem controls ordinal stage families and
replaces the prior local existential package.
-/

@[expose] public section

@[stacks 0GS0] #check @Ordinal.ToType.exists_upperBound_of_lift_mk_lt_cof

#check @CategoryTheory.Precoverage.hasCardinalLTCoveringPresieves
