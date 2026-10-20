/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.SheafTheoreticEmpty

/-!
# Definition 7.42.1

The intrinsic bottom-sieve owner and the sheafified-representable presentation
are reusable site API, so this source file is a tagged recall.
-/

@[expose] public section

/- Definition 7.42.1 (04B5): an object is sheaf-theoretically empty exactly
when its sheafified representable is initial. -/
@[stacks 04B5] #check @CategoryTheory.GrothendieckTopology.IsSheafTheoreticallyEmpty

#check @CategoryTheory.GrothendieckTopology.isSheafTheoreticallyEmpty_iff_nonempty_isInitial
