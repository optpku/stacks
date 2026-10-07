module

public import Mathlib.CategoryTheory.Opposites
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
Definition 4.3.1: for a category `C`, the opposite category `Cᵒᵖ` has the same objects as `C`
and all morphisms reversed. This is the canonical mathlib instance `Category.opposite`.
-/
@[stacks 001M "opposite category with the same objects and reversed morphisms"]
#check (Category.opposite (C := C) : Category.{v} Cᵒᵖ)

end CategoryTheory
