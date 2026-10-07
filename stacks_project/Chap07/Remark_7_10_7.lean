module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Sheafification.MatchingFamily

@[expose] public section

/-!
# Remark 7.10.7

The mutual-refinement transport for concrete matching families is owned by the
generic sheafification API.
-/

/- Remark 7.10.7 (00W8): matching families on mutually refining covers are
canonically equivalent. -/
@[stacks 00W8] #check @CategoryTheory.GrothendieckTopology.Meq.mutualRefinementEquiv

#check @CategoryTheory.GrothendieckTopology.Meq.mutualRefinementEquiv_def
