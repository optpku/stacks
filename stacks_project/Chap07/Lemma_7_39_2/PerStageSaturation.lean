module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Advance

/-!
# One-step saturation

Uniform choices of a further separating stage belong to
`OrderedRefinement.Saturation.Advance`.  This removes the Chapter-local
Zorn-style stage-under-a-base wrapper from the reusable surface.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "per-stage saturation"] #check @OrderedRefinement.Saturation.Advance
#check @OrderedRefinement.Saturation.Advance.ofExists
#check @OrderedRefinement.Saturation.Advance.ofExists.realizes
#check @OrderedRefinement.Saturation.Advance.toExists
