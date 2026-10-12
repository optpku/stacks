/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled

/-!
# Scheduled saturation interface

This chapter entry recalls the direct ReasLib interface for a request-indexed
terminal witness and its coherent scheduled diagram.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "finite scheduled terminal stage"] #check @OrderedRefinement.Saturation.Stage.Scheduled.Terminal
#check @OrderedRefinement.Saturation.Stage.Scheduled.Terminal.toExists
#check @OrderedRefinement.Saturation.Stage.Scheduled.Terminal.ofExists

@[stacks 00YP "finite scheduled saturation diagram"] #check @OrderedRefinement.Saturation.Stage.Scheduled.Diagram
#check @OrderedRefinement.Saturation.Stage.Scheduled.Diagram.ofTerminal
#check @OrderedRefinement.Saturation.Stage.Scheduled.Diagram.toTerminal
