module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.OpenTower

/-!
# Open scheduled recursion

An `OpenTower` is the reusable owner for the coherent data of all recursive
cuts.  It replaces the former node-by-node Chapter-specific structure.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "recursive saturation node"] #check @OrderedRefinement.Saturation.Stage.Scheduled.OpenTower
#check @OrderedRefinement.Saturation.Stage.Scheduled.OpenTower.ofDiagram
#check @OrderedRefinement.Saturation.Stage.Scheduled.OpenTower.toTopPrefix
#check @OrderedRefinement.Saturation.Stage.Scheduled.OpenTower.toTerminal
