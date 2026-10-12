/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.RefinementDiagram

/-!
# Refinement-stage telescope bridge

`OrderedRefinement.Saturation.RefinementStage.Diagram` is the reusable
source-factorized form of a directed refinement diagram.  It replaces the
old explicit representative preorder and its local instance reconstruction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "directed refinement-stage limit"] #check @OrderedRefinement.Saturation.RefinementStage.Diagram.toTargetDiagram
#check @OrderedRefinement.Saturation.RefinementStage.Diagram.telescopeRefinement
#check @OrderedRefinement.Saturation.RefinementStage.Diagram.telescopeStage
#check @OrderedRefinement.Saturation.RefinementStage.Diagram.telescopeInclusion
