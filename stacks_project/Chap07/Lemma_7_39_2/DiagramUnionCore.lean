/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Specialization.Diagram

/-!
# Coherent saturation-stage diagrams

The reusable owner for a based coherent diagram of scheduled separating
stages is `OrderedRefinement.Saturation.Stage.Diagram`.  It replaces the
former Chapter-specific `Refinement.Diagram` and its duplicate coherence
fields.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "coherent saturation-stage diagram"] #check @OrderedRefinement.Saturation.Stage.Diagram
#check @OrderedRefinement.Saturation.Stage.Diagram.stage
#check @OrderedRefinement.Saturation.Stage.Diagram.hom
#check @OrderedRefinement.Saturation.Stage.Diagram.fromBase
#check @OrderedRefinement.Saturation.Stage.Diagram.toTargetDiagram
#check @OrderedRefinement.Saturation.Stage.Diagram.toRefinementDiagram
