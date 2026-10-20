/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.PresheafFiber
public import StacksCheckRecall.CommandCrossRef

/- Lemma 7.32.3 (00Y6), equation (7.32.3.1): the presheaf costalk construction is owned by
`ReasLib.CategoryTheory.Functor.PresheafFiber`. -/
@[stacks 00Y6 "equation (7.32.3.1)"] #check @CategoryTheory.Functor.presheafCostalk
