/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Precoverage.QuasiContinuous

import StacksCheckRecall

@[expose] public section

/-! [stacks 00X8 (1)]
The quasi-continuity finite-limit criterion is owned by the selected-precoverage API. -/
@[stacks 00X8 "(1)"] #check @CategoryTheory.Functor.Precoverage.IsQuasiContinuous
#check @CategoryTheory.Functor.Precoverage.IsQuasiContinuous.toMorphismOfSites

/-! [stacks 00X8 (2)]
The exactness clause is the corresponding reusable sheaf-pullback criterion. -/
@[stacks 00X8 "(2)"] #check @CategoryTheory.Functor.Precoverage.IsQuasiContinuous.exactSheafPullback
