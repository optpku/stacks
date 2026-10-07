module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.OpenTower

/-!
# Terminal and open-tower equivalences

The adapters between terminal witnesses, top prefixes, and open towers live
in the reusable ReasLib open-tower API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "terminal-to-open-tower bridge"] #check @OrderedRefinement.Saturation.Stage.Scheduled.OpenTower.equivTopPrefix
#check @OrderedRefinement.Saturation.Stage.Scheduled.OpenPrefix.toTower
#check @OrderedRefinement.Saturation.Stage.Scheduled.Terminal.toOpenTower
