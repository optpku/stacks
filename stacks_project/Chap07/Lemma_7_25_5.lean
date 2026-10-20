/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef

public import ReasLib.CategoryTheory.Sites.Localization.LowerShriek
import StacksCheckRecall

@[expose] public section

/- Lemma 7.25.5 (04BB): localization lower shriek preserves finite connected limits, hence
pullbacks and equalizers. -/
@[stacks 04BB "(1)"] #check @CategoryTheory.GrothendieckTopology.Localization.LowerShriek.preservesFiniteConnectedLimits

@[stacks 04BB "(2)"] #check @CategoryTheory.GrothendieckTopology.Localization.LowerShriek.preservesPullbacks

@[stacks 04BB "(3)"] #check @CategoryTheory.GrothendieckTopology.Localization.LowerShriek.preservesEqualizers
