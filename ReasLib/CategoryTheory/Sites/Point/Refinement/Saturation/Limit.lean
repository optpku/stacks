/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Limit.Stage
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Limit.Inclusion
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Limit.Cocone

/-!
# Telescope limits of saturation-stage diagrams

This umbrella exports telescope stages, their component inclusions, the
standard categorical cocone, and the canonical leg from a based diagram's
source.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement.Saturation

end OrderedRefinement.Saturation
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
