/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Extension
import StacksCheckRecall

@[expose] public section

-- Remark 13.35.6: supremum formulas for additive, retract, shift, and extension closures are
-- owned by the reusable object-property extension API.
@[stacks 0FX6] #check @CategoryTheory.ObjectProperty.shiftInterval_iSup

@[stacks 0FX6] #check @CategoryTheory.ObjectProperty.retractClosure_iSup

@[stacks 0FX6] #check @CategoryTheory.ObjectProperty.additiveClosure_iSup_of_monotone

@[stacks 0FX6] #check @CategoryTheory.ObjectProperty.extensionProduct_iSup_left

@[stacks 0FX6] #check @CategoryTheory.ObjectProperty.extensionProduct_iSup_right

@[stacks 0FX6] #check @CategoryTheory.ObjectProperty.extensionProduct_iSup_of_monotone

@[stacks 0FX6] #check @CategoryTheory.ObjectProperty.extensionProductIter_iSup_of_monotone
