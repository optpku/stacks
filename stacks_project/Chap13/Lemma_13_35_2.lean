module

import Mathlib.CategoryTheory.Triangulated.Subcategory
import StacksCheckRecall

@[expose] public section

-- Lemma 13.35.2: retract closure and the extension product are already owned by Mathlib.
@[stacks 0FX2] #check @CategoryTheory.ObjectProperty.extensionProduct_retractClosure_retractClosure_le
#check @CategoryTheory.ObjectProperty.retractClosure_extensionProduct_retractClosure_retractClosure
