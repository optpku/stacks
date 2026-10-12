/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Basic

/-!
# Scheduled saturation data

Terminal witnesses and bottom-indexed scheduled diagrams are the canonical
ReasLib data owners.  The Chapter-local duplicate wrapper has been removed.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "bottom-indexed saturation diagram"] #check @OrderedRefinement.Saturation.Stage.Scheduled.Terminal
#check @OrderedRefinement.Saturation.Stage.Scheduled.Terminal.ofExists
#check @OrderedRefinement.Saturation.Stage.Scheduled.Diagram
#check @OrderedRefinement.Saturation.Stage.Scheduled.Diagram.ofDiagram
#check @OrderedRefinement.Saturation.Stage.Scheduled.Diagram.ofTerminal
#check @OrderedRefinement.Saturation.Stage.Scheduled.Diagram.toTerminal
