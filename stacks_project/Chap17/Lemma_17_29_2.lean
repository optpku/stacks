/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialOperator
import StacksCheckRecall

@[expose] public section

/- Lemma 17.29.2 (0G3R): composing differential operators adds their order bounds. -/
@[stacks 0G3R]
#check @SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder.comp
