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
/- Definition 4.4.2: a category has products of pairs when it has a product for every pair of
objects; this is the canonical mathlib class `CategoryTheory.Limits.HasBinaryProducts`. -/
@[stacks 001T "products for every pair of objects"]
#check (HasBinaryProducts C : Prop)

end CategoryTheory.Limits
