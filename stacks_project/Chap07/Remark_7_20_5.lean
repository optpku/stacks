module

public import ReasLib.CategoryTheory.Sites.Precoverage.CoverLifting
public import StacksCheckRecall.CommandCrossRef

/-!
# Remark 7.20.5

The selected-cover lifting property is reusable precoverage API, independent
of the Chapter 7 presentation.
-/

@[expose] public section

/- Remark 7.20.5 (09W7): selected target covers lift along maps from image
objects to selected source covers, and this lifting condition induces
cocontinuity for the generated topologies. -/
@[stacks 09W7 "lifting"] #check @CategoryTheory.Functor.Precoverage.HasCoverLifts

@[stacks 09W7 "cocontinuity"] #check @CategoryTheory.Functor.Precoverage.HasCoverLifts.toCocontinuous
