/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Diagram.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Diagram.Operations
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Diagram.Preorder

/-!
# Based diagrams of saturation stages

This umbrella exports the basic based-diagram owner, its constant and reindexing
API, and the optional bridge to diagrams of directed preorder systems.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement.Saturation

end OrderedRefinement.Saturation
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
