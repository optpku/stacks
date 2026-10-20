/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Limit

/-!
# Telescope limits of saturation diagrams

The source-sensitive telescope limit is owned by
`OrderedRefinement.Saturation.Stage.Diagram`.  Its anchor, component
inclusions, and based cocone replace the former Chapter-local direct-union
construction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "bundled diagram limit stage"] #check @OrderedRefinement.Saturation.Stage.Diagram.TelescopeAnchor
#check @OrderedRefinement.Saturation.Stage.Diagram.telescopeStage
#check @OrderedRefinement.Saturation.Stage.Diagram.telescopeInclusion
#check @OrderedRefinement.Saturation.Stage.Diagram.telescopeCocone
#check @OrderedRefinement.Saturation.Stage.Diagram.underTelescopeCocone
