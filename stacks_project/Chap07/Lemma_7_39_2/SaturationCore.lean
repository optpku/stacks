module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation

/-!
# Reusable saturation core

The public core is stratified by mathematical data: `Target` for finite-cover
lifting, `RefinementStage` for a fixed source factorization, and `Stage` when
separation and solved-request data are also required.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "stagewise saturation existence"] #check @OrderedRefinement.Saturation.Advance
#check @OrderedRefinement.Saturation.Advance.ofExists
#check @OrderedRefinement.Saturation.Advance.toExists

@[stacks 00YP "generic stagewise saturation existence"] #check @OrderedRefinement.Saturation.RefinementStage.Advance
#check @OrderedRefinement.Saturation.RefinementStage.Advance.ofExists
#check @OrderedRefinement.Saturation.RefinementStage.Advance.toExists

@[stacks 00YP "terminal refinement stage"] #check @OrderedRefinement.Saturation.Tower
#check @OrderedRefinement.Saturation.Tower.telescopeTargetComplete
#check @OrderedRefinement.Saturation.Tower.telescopeStage.targetComplete
