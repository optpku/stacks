module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Extension.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Extension.Computations
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Extension.GluingComputations
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Extension.Section
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Extension.Telescope
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Extension.TelescopeComputations

/-!
# Arbitrary-cut scheduled saturation extensions

This umbrella exports the neutral owner and computation API for adjoining a
stage to a based diagram on all strict predecessors of an arbitrary cut.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement.Saturation.Stage.Scheduled

end OrderedRefinement.Saturation.Stage.Scheduled
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
