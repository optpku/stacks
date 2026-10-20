/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.BeckChevalley
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.27.5

The slice reindexing square, its induced sheaf pullback square, and the
Beck--Chevalley comparison are reusable categorical infrastructure.  This
source-facing file recalls their canonical ReasLib owners.
-/

@[expose] public section

/- Lemma 7.27.5 (0EYV) (1): a commutative square in a category induces the
canonical square of slice reindexing functors. -/
@[stacks 0EYV "(1)"] #check @CategoryTheory.Over.mapCommSq

/- Lemma 7.27.5 (0EYV) (2): inverse-image functors on the four slice sites
commute around this square. -/
@[stacks 0EYV "(2)"] #check @CategoryTheory.GrothendieckTopology.overMapPullbackSquare

/- Lemma 7.27.5 (0EYV) (3): a cartesian slice square is Guitart exact, so the
associated Beck--Chevalley comparison is invertible. -/
@[stacks 0EYV "(3)"] #check @CategoryTheory.Over.mapCommSq_guitartExact_of_isPullback

@[stacks 0EYV "(3)"] #check @CategoryTheory.CatCommSq.BeckChevalley.comparison

@[stacks 0EYV "(3)"] #check @CategoryTheory.CatCommSq.BeckChevalley.comparison_isIso_of_guitartExact
