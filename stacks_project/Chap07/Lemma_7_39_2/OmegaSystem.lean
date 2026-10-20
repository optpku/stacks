module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Tower

/-!
# Sequential saturation towers

The reusable natural-number tower owns derived transition maps and its based
diagram.  It supersedes the Chapter-local omega index and system construction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "omega refinement tower"] #check @OrderedRefinement.Saturation.Tower
#check @OrderedRefinement.Saturation.Tower.hom
#check @OrderedRefinement.Saturation.Tower.toDiagram
#check @OrderedRefinement.Saturation.Tower.ofAdvance
