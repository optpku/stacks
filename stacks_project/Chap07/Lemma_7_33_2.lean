/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Fiber.FiniteLimits

/-!
# Lemma 7.33.2

The terminal-fiber and pullback-comparison criterion is generic ReasLib API.
This chapter file retains only the source-labeled recall.
-/

@[expose] public section

/- Lemma 7.33.2 (00YB): a set-valued functor on a category with a final object and fibred
products has cofiltered category of elements when its terminal fiber is a singleton and all
pullback comparisons are bijections.  For a small category of elements, the associated sheaf
fiber is left exact. -/
@[stacks 00YB] #check @CategoryTheory.FunctorToTypes.Elements.isCofiltered_of_terminal_and_pullbacks

#check @CategoryTheory.FunctorToTypes.PullbackComparison.bijective
#check @CategoryTheory.FunctorToTypes.FiniteLimits.of_terminal_and_pullbacks
#check @CategoryTheory.GrothendieckTopology.Point.Fiber.Stalk.preservesFiniteLimits
