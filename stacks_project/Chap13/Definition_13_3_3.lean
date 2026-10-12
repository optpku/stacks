/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.CategoryTheory.Triangulated.Functor
import StacksCheckRecall

@[expose] public section

/-!
# Source-facing bridge for Definition 13.3.3

An exact functor is modeled by its shift-commuting data `Functor.CommShift ℤ`
together with the distinguished-triangle preservation property
`Functor.IsTriangulated`.
-/

namespace CategoryTheory

@[stacks 014V] #check @Functor.CommShift
#check @Functor.IsTriangulated
#check @Functor.mapTriangle
#check @Functor.mapTriangleCompIso

end CategoryTheory
