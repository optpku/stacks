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

/- Lemma 7.38.5 (06UL): enough points are local for a family covering the terminal object,
provided every corresponding slice site has enough points. -/
@[stacks 06UL] #check @HasEnoughPoints.of_coversTop

end CategoryTheory.GrothendieckTopology
