/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Localization.LowerShriek
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.35.3

The coefficient-general lower-shriek fiber decomposition is owned by ReasLib;
this Chapter 7 entry retains the Type-valued source formulation.
-/

@[expose] public section

/- Lemma 7.35.3 (04H4): the fiber at `p` of `j_{U!} G` is the coproduct, hence for `Type` the
sigma type, of the fibers of `G` at the localized points `p.over x`. -/
@[stacks 04H4] #check @CategoryTheory.GrothendieckTopology.Point.Localization.lowerShriekFiber_isomorphic_sigma
