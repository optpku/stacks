/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Reindexing.PresheafFiber
public import ReasLib.CategoryTheory.Sites.Point.Reindexing.OrderEmbedding.Fiber
public import ReasLib.CategoryTheory.Sites.Point.OrderedRefinement.Fiber
public import ReasLib.CategoryTheory.Sites.Point.OrderedRefinement.EssentiallySmall.Cofiltered

/-!
# Fibers of reindexed inverse systems

Compatibility umbrella for the fiber and presheaf-fiber API of reindexed
inverse systems.  New downstream modules should import the narrow owner module
for the abstraction layer they use.
-/
