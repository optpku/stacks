/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Transfer
import StacksCheckRecall

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [HasFiniteProducts A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (a : A ⥤ B) (b : B ⥤ A) [a.Additive] [b.Additive]
  [PreservesFiniteLimits b]
variable (i : a ⋙ b ≅ 𝟭 A) (adj : b ⊣ a)

/- Lemma 12.7.4 [03A3]: an additive category is abelian when it is an
adjoint retract of an abelian category through a left-exact additive functor. -/
@[stacks 03A3]
#check (abelianOfAdjunction a b i adj : Abelian A)

end CategoryTheory
