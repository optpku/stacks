module

public import Mathlib.CategoryTheory.Abelian.Basic
public import ReasLib.CategoryTheory.Monoidal.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness of the zero object

In an abelian monoidal category whose tensor product is additive, tensoring with the zero object
is the zero exact functor.
-/

@[expose] public section

open CategoryTheory Limits
open scoped ZeroObject

universe u v

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasZeroObject C]
variable [MonoidalCategory C] [MonoidalPreadditive C]

/-- The zero object of an abelian monoidal category is flat. -/
@[stacks 03ER "zero object", instance]
theorem zero_isFlat : IsFlat (0 : C) := sorry

end CategoryTheory.MonoidalCategory
