/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
import StacksCheckRecall

@[expose] public section

/- Lemma 17.16.3 (01CC): right tensoring by a fixed closed object in a braided monoidal category
is right exact.  Module sheaves are the source specialization. -/
@[stacks 01CC]
#check @CategoryTheory.MonoidalClosed.tensorRight_rightExact
