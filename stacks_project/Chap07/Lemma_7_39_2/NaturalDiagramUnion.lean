module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Limit

/-!
# Natural telescope cocones

The canonical component-to-telescope maps form a cocone in ReasLib, including
its based `Under` formulation.  No Chapter-specific cone packaging is needed.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

@[stacks 00YP "compatible packaged-stage cone"] #check @OrderedRefinement.Saturation.Stage.Diagram.telescopeCocone
#check @OrderedRefinement.Saturation.Stage.Diagram.baseToTelescope
#check @OrderedRefinement.Saturation.Stage.Diagram.baseToTelescope.fac
#check @OrderedRefinement.Saturation.Stage.Diagram.underTelescopeCocone
