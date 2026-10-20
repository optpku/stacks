module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import StacksCheckRecall

@[expose] public section


universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y Z : C} {a b : X ⟶ Y} {e : Z ⟶ X} {h : e ≫ a = e ≫ b}

/- `Fork.ofι e h` packages the source morphism and equalizing equation, while
`IsLimit (Fork.ofι e h)` gives exactly its existence-and-uniqueness factorization property.
The verified alternatives `Fork.IsLimit.existsUnique` and `Fork.IsLimit.ofExistsUnique` are the
two source/core bridge directions, and `Fork.IsLimit.homIso` is a stronger natural bijection, so
none should replace the canonical owner. This choice generalizes only by exposing the standard
limiting-fork structure; the textbook definition is recovered using `Fork.ι_ofι`, and later
entries can reuse the full limit-cone API without a local wrapper. -/

/- Definition 4.10.1: for parallel morphisms `a b : X ⟶ Y`, the textbook notion that
`e : Z ⟶ X` with `h : e ≫ a = e ≫ b` is an equalizer of `(a, b)` is exactly the canonical
mathlib notion that the fork `Fork.ofι e h` is limiting. -/
@[stacks 0028 "equalizing morphism with its universal factorization property"]
#check (IsLimit (Fork.ofι e h) : Type (max u v))

/- Companion recall: the unique-factorization clause in the textbook definition is the canonical
theorem `Fork.IsLimit.existsUnique`. -/
#check Fork.IsLimit.existsUnique

/- Companion recall: the converse direction is the canonical constructor
`Fork.IsLimit.ofExistsUnique`. -/
#check Fork.IsLimit.ofExistsUnique

end CategoryTheory.Limits
