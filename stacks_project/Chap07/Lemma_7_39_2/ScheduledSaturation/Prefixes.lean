/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix

/-!
# Scheduled saturation prefixes

Closed and open cuts, their restriction API, and telescope extensions are
owned by the ReasLib scheduled-prefix hierarchy.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "closed saturation prefix"] #check @OrderedRefinement.Saturation.Stage.Scheduled.Prefix
#check @OrderedRefinement.Saturation.Stage.Scheduled.Prefix.bottom
#check @OrderedRefinement.Saturation.Stage.Scheduled.Prefix.toScheduledDiagram

@[stacks 00YP "open saturation prefix"] #check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix
#check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.ofMin
#check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.CutExtension
#check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.CutExtension.toTerminal

@[stacks 00YP "open saturation tower"] #check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.toTerminal
#check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.toTerminalDiagram
