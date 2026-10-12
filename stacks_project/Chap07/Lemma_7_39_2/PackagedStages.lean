/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Stage

/-!
# Scheduled separating refinement stages

`OrderedRefinement.Saturation.Stage` is the canonical owner for a refinement
of a fixed inverse system that retains both separation data and solved
finite-cover requests.  The former sheaf-specialized `Refinement.Stage`
wrapper duplicated this data and is deliberately not retained.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "scheduled separating refinement stage"] #check @OrderedRefinement.Saturation.Stage
#check @OrderedRefinement.Saturation.Stage.system
#check @OrderedRefinement.Saturation.Stage.toRefinement
#check @OrderedRefinement.Saturation.Stage.mapRequest
#check @OrderedRefinement.Saturation.Stage.solves
#check @OrderedRefinement.Saturation.Stage.Hom
#check @OrderedRefinement.Saturation.Stage.Hom.mapRequest
#check @OrderedRefinement.Saturation.Stage.Hom.realizesAll
