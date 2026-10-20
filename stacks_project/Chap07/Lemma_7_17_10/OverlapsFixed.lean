module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 fixed-overlap recall

The temporary fixed-target overlap witness was tailored to one proof route and
is not retained as reusable data.  The cardinal cover interface retains the
stable presentation data needed downstream.
-/

@[expose] public section

@[stacks 0GS0] #check @CategoryTheory.Presieve.GeneratingFamily.ofUncurry

#check @CategoryTheory.Precoverage.hasCardinalLTCoveringPresieves
