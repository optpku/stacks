/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.TargetDiagram.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.TargetDiagram.Telescope
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.TargetDiagram.Completion
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.TargetDiagram.Cocone

/-!
# Directed diagrams of finite-cover saturation targets

This umbrella exports the source-free target-diagram telescope, its component
inclusions and request transport, and the standard categorical cocone.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement.Saturation

end OrderedRefinement.Saturation
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
