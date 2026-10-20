/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.Generation.Generated
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty

-- Remark 13.36.7: the closure statement is the object-level bridge from membership of `E` to
-- containment of its canonical triangulated envelope.
@[stacks 0ATH] #check @CategoryTheory.ObjectProperty.Generated.Property.le_of_mem
