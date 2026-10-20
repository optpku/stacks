/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Preadditive.CompactObject
import StacksCheckRecall

@[expose] public section

open CategoryTheory

-- Definition 13.37.1: compactness is a preadditive-category notion, not a derived-category
-- wrapper. The canonical owner is directly importable from ReasLib.
@[stacks 07LS] #check @CategoryTheory.IsCompactObject
#check @CategoryTheory.isCompactObject_zero
