module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
variable [Preadditive C] [HasFiniteProducts C]

/- Definition 12.17.1: the tensor product of an additive monoidal category is additive in each
variable.  Mathlib owns this condition as `MonoidalPreadditive C`; the surrounding
`Preadditive C` and `HasFiniteProducts C` are the canonical additive-category assumptions. -/
@[stacks 0FNA] #check MonoidalPreadditive C

/- The owner exposes additive tensoring functors directly through typeclass inference. -/
#check tensorLeft_additive
#check tensorRight_additive

end CategoryTheory
