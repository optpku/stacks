/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation

/-!
# Saturation API

This is a chapter-local recall of the stable ReasLib saturation surface.  It
does not re-export Chapter 7 implementation details or create a reverse
dependency from the reusable library to the chapter.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "stable saturation API"] #check @OrderedRefinement.Saturation.Target
#check @OrderedRefinement.Saturation.Target.Hom.realizesAll
#check @OrderedRefinement.Saturation.Target.Diagram.TelescopeTarget
#check @OrderedRefinement.Saturation.RefinementStage
#check @OrderedRefinement.Saturation.RefinementStage.Advance
#check @OrderedRefinement.Saturation.Stage
#check @OrderedRefinement.Saturation.Stage.Diagram.telescopeStage
#check @OrderedRefinement.Saturation.Stage.Scheduled.Terminal
#check @OrderedRefinement.Saturation.Advance
#check @OrderedRefinement.Saturation.Tower
