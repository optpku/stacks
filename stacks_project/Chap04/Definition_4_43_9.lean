/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/- Definition 4.43.9: the Stacks notion of a symmetric monoidal category is the canonical
mathlib class `SymmetricCategory C`. Concretely, on top of the fixed monoidal structure, this is
a braided structure whose braiding is involutive. -/
@[stacks 0FFW "symmetric monoidal category via an involutive braiding"]
#check (SymmetricCategory C : Type (max u v))

end CategoryTheory
