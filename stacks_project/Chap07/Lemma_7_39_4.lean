/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Enough

@[expose] public section

namespace CategoryTheory.GrothendieckTopology

/- Lemma 7.39.4 (0DW0): a family covering the terminal object gives enough points when each
slice site has finite limits and the finite-refinement property.  This is the reusable
cover-local composition of the finite-refinement and enough-points APIs. -/
@[stacks 0DW0] #check @HasEnoughPoints.of_coversTop_of_slice_finiteRefinement

end CategoryTheory.GrothendieckTopology
