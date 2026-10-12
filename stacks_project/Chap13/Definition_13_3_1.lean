/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.CategoryTheory.Triangulated.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Source-facing bridge for Definition 13.3.1

The triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` and its morphisms are already the canonical
mathlib objects `Triangle` and `TriangleMorphism`; this item deliberately adds
no chapter-local wrapper.
-/

namespace CategoryTheory.Pretriangulated

@[stacks 0144] #check @Triangle
#check @Triangle.mk
#check @TriangleMorphism
#check @Triangle.homMk

end CategoryTheory.Pretriangulated
