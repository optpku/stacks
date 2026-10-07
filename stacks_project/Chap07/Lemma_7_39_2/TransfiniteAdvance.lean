module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Successor.Gluing

/-!
# Transfinite scheduled advances

The reusable transfinite recursion surface is the scheduled-prefix extension
API.  It keeps a cut's concrete cocone and realization data together, rather
than exposing a Chapter-local chain of transports and local instances.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "legacy transfinite saturation advance"] #check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.CutExtension
#check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.CutExtension.toPrefix
#check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.CutExtension.toTerminal

@[stacks 00YP "legacy compatible transfinite saturation tower"] #check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.SuccExtension
#check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.SuccExtension.toPrefix.restrict

@[stacks 00YP "legacy terminal refinement stage"] #check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.toTerminal
