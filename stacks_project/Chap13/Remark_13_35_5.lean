module

import ReasLib.CategoryTheory.Pretriangulated.Extension
import StacksCheckRecall

@[expose] public section

-- Remark 13.35.5: functoriality of shift, additive, retract, and extension closures is owned by
-- the reusable object-property extension API.
@[stacks 0FX5] #check @CategoryTheory.ObjectProperty.objectShiftInterval

@[stacks 0FX5] #check @CategoryTheory.ObjectProperty.shiftInterval

@[stacks 0FX5] #check @CategoryTheory.ObjectProperty.map_shiftInterval

@[stacks 0FX5] #check @CategoryTheory.ObjectProperty.map_retractClosure_le

@[stacks 0FX5] #check @CategoryTheory.ObjectProperty.map_additiveClosure_le

@[stacks 0FX5] #check @CategoryTheory.ObjectProperty.map_extensionProduct_le

@[stacks 0FX5] #check @CategoryTheory.ObjectProperty.map_extensionProductIter_le

@[stacks 0FX5] #check @CategoryTheory.ObjectProperty.map_additiveExtensionStage_le
