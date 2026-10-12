/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
import StacksCheckRecall

@[expose] public section

/-!
# Definition 13.40.1

Right and left orthogonals are the canonical Mathlib object properties
`ObjectProperty.rightOrthogonal` and `ObjectProperty.leftOrthogonal`; no
chapter-local notation is needed.
-/

namespace CategoryTheory.ObjectProperty

@[stacks 0FXB] #check @rightOrthogonal

@[stacks 0FXB] #check @leftOrthogonal

#check @rightOrthogonal_iff
#check @leftOrthogonal_iff

end CategoryTheory.ObjectProperty
