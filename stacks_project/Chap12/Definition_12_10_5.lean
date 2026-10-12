/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import StacksCheckRecall

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace ExactFunctor

section

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable (F : A ⥤ₑ B)

/- Definition 12.10.5 [02MR]: the kernel of an exact functor is the canonical object property of
objects sent to zero. -/
@[stacks 02MR]
#check (F.obj.kernel : ObjectProperty A)

/- The corresponding full subcategory is obtained directly from that object property. -/
#check F.obj.kernel.FullSubcategory

end

end ExactFunctor

end CategoryTheory
