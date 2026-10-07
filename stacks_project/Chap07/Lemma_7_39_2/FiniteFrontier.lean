module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix

/-!
# Finite scheduled frontiers

Finite request frontiers are initial segments of the general scheduled-stage
construction.  ReasLib records the schedule as `Stage.Scheduled.Prefix`,
instead of exposing separate Chapter-only List and Finset existence wrappers.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "finite scheduled frontier"] #check @OrderedRefinement.Saturation.Stage.Scheduled.Prefix
#check @OrderedRefinement.Saturation.Stage.Scheduled.Prefix.bottom
#check @OrderedRefinement.Saturation.Stage.Scheduled.Prefix.bottomRealizes
#check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.toTerminal
#check @OrderedRefinement.Saturation.Stage.Scheduled.Terminal
