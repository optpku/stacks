/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y P : C} {p : P ⟶ X} {q : P ⟶ Y}

/-
The source fixes `P`, `p`, and `q` and asks for the unique mediating-map property. The verified
owners `BinaryFan.mk` and `IsLimit` package exactly that data and property;
`IsLimit.existsUnique` exposes the source-shaped view, while `BinaryFan.isLimitMk` is the converse
constructor. The existence proposition `HasBinaryProduct X Y` would forget the specified object
`P` and projections `p` and `q`. For `w`, `α`, and `β`, the source statement is recovered by
using the competing fan `BinaryFan.mk α β`. This introduces no generalization and gives
downstream developments the full limit-cone API without a project-local wrapper.
-/

/- Definition 4.4.1: morphisms `p : P ⟶ X` and `q : P ⟶ Y` exhibit `P` as a product of `X` and
`Y` precisely when the binary fan `BinaryFan.mk p q` is limiting. -/
@[stacks 001S "product object and projections with the unique mediating-map property"]
#check (IsLimit (BinaryFan.mk p q) : Type (max u v))

/- Companion recall: the unique-factorization clause in the textbook definition is the canonical
theorem `IsLimit.existsUnique`. -/
#check IsLimit.existsUnique

/- Companion recall: the converse direction from the textbook `∃!` universal property to a
limiting binary fan is the binary-product-specific constructor `BinaryFan.isLimitMk`. -/
#check BinaryFan.isLimitMk

end CategoryTheory.Limits
