/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.ObjectProperty.Orthogonal.Retract
import StacksCheckRecall.CommandCrossRef

@[expose] public section

/- Lemma 13.40.4 (Stacks 0FXC): both canonical orthogonals of an object
property are stable under retracts. -/

@[stacks 0FXC]
#check @CategoryTheory.ObjectProperty.RightOrthogonal.stableUnderRetracts

@[stacks 0FXC]
#check @CategoryTheory.ObjectProperty.LeftOrthogonal.stableUnderRetracts
