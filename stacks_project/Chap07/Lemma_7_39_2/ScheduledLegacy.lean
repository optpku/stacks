/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Step

/-!
# One-request scheduled extension

The reusable owner for a successor that realizes one request after a fixed
base map is `OrderedRefinement.Saturation.Stage.Scheduled.Step`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "legacy scheduled successor"] #check @OrderedRefinement.Saturation.Stage.Scheduled.Step
#check @OrderedRefinement.Saturation.Stage.Scheduled.Step.fromBase
#check @OrderedRefinement.Saturation.Stage.Scheduled.Step.ofLocal
#check @OrderedRefinement.Saturation.Stage.Scheduled.Step.toExists
