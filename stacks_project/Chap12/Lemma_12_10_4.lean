/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
import StacksCheckRecall

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ₑ B)

/- Lemma 12.10.4 [02MQ]: the kernel object property of an exact functor is a Serre class. This is
the canonical inverse-image instance, so no chapter-local theorem wrapper is needed. -/
@[stacks 02MQ]
#check (inferInstance : F.obj.kernel.IsSerreClass)

end CategoryTheory
