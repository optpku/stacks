/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
