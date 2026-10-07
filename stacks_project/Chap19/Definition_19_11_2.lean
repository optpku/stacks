module

public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.SetTheory.Cardinal.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (M : C)

/- Definition 19.11.2: the size of an object `M` is the cardinality of its type of subobjects.
This canonical expression already makes sense in any category. -/
@[stacks 079C]
#check (Cardinal.mk (Subobject M) : Cardinal)

end
