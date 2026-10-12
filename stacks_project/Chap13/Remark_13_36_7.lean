/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
