/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.CategoryTheory.Triangulated.Triangulated
import StacksCheckRecall

@[expose] public section

/-!
# Source-facing bridge for Definition 13.3.2

Mathlib separates the distinguished-triangle structure satisfying TR1--TR3
(`Pretriangulated`) from the additional octahedral condition (`IsTriangulated`).
This is the canonical formal decomposition of the source definition.
-/

namespace CategoryTheory

@[stacks 0145] #check @Pretriangulated
#check @IsTriangulated
#check @IsTriangulated.mk'

end CategoryTheory
