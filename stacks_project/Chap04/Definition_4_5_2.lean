module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

/-
Definition 4.5.2: a category has coproducts of pairs when every pair of objects admits a
coproduct. This is the canonical mathlib typeclass `HasBinaryCoproducts`.
-/
@[stacks 04AP "categories with coproducts of every pair of objects"]
#check (HasBinaryCoproducts C : Prop)

end CategoryTheory.Limits
