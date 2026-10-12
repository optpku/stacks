/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Computations
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Extension
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.RestrictionFunctor
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Section
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Successor

/-!
# Initial-segment scheduled saturation

This umbrella exports the reusable data, operations, and computation API for
closed and open initial segments of scheduled saturation diagrams.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement.Saturation.Stage.Scheduled

end OrderedRefinement.Saturation.Stage.Scheduled
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
