/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous
public import StacksCheckRecall.CommandCrossRef

/-!
# Definition 7.42.3

The source notion is owned by the reusable site-functor API.  This chapter
file records the tagged textbook entry and recalls its canonical interface.
-/

@[expose] public section

/- Definition 7.42.3 (04B7): an almost cocontinuous functor admits a covering
almost pullback for every covering sieve. -/
@[stacks 04B7] #check @CategoryTheory.Functor.IsAlmostCocontinuous
#check @CategoryTheory.Functor.almost_cover_lift
#check @CategoryTheory.Functor.cover_lift_factors
