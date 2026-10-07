module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Tower

/-!
# Completion of sequential saturation towers

Target completion and anchored telescope completion are generic consequences
of a ReasLib saturation tower's eventual-realization invariant.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "omega refinement terminal system"] #check @OrderedRefinement.Saturation.Tower.telescopeTargetComplete

@[stacks 00YP "omega refinement advance"] #check @OrderedRefinement.Saturation.Tower.ofAdvance

@[stacks 00YP "omega tower separation"] #check @OrderedRefinement.Saturation.Tower.toDiagram

@[stacks 00YP "omega tower request realization"] #check @OrderedRefinement.Saturation.Tower.eventuallyRealizes
#check @OrderedRefinement.Saturation.Tower.telescopeStage.targetComplete
