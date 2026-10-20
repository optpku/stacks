/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialOperator
import StacksCheckRecall

@[expose] public section

/- Definition 17.29.1 (0G3Q): differential operators between module sheaves are defined
objectwise over the corresponding morphism of section rings. -/
@[stacks 0G3Q]
#check @SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder

#check @SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder.app
