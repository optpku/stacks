/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.HomotopyCategory.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Object-level factorization through the homotopy category

At the level of objects, functors from the homotopy category are equivalent to pseudofunctors
from the original bicategory into a locally discrete bicategory. This file does not claim a
StrongTrans/Modification-level equivalence.
-/

@[expose] public section

universe w v u vD uD

namespace CategoryTheory.Bicategory.HomotopyCategory

open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {D : Type uD} [Category.{vD} D]

namespace lift

/-- Lifting the pseudofunctor induced by a functor from the homotopy category recovers that
functor. -/
@[simp]
theorem quotient (G : Functor (Bicategory.HomotopyCategory B) D) :
    lift (Pseudofunctor.comp (HomotopyCategory.quotient B) G.toPseudofunctor) = G := sorry

end lift

variable (B D) in
/-- At the object level, functors out of the homotopy `1`-category are equivalent to
pseudofunctors from `B` into the locally discrete bicategory on the target category. -/
@[stacks 04SC "object-level factorization through the homotopy category"]
def functorEquiv :
    Functor (Bicategory.HomotopyCategory B) D ≃ Pseudofunctor B (LocallyDiscrete D) where
  toFun G := Pseudofunctor.comp (HomotopyCategory.quotient B) G.toPseudofunctor
  invFun F := lift F
  left_inv := lift.quotient
  right_inv := lift.fac

namespace functorEquiv

/-- The forward map in the factorization equivalence is composition with the quotient
pseudofunctor. -/
@[simp]
theorem apply (G : Functor (Bicategory.HomotopyCategory B) D) :
    functorEquiv B D G =
      Pseudofunctor.comp (HomotopyCategory.quotient B) G.toPseudofunctor := sorry

/-- The inverse map in the factorization equivalence is descent to the homotopy category. -/
@[simp]
theorem symm_apply (F : Pseudofunctor B (LocallyDiscrete D)) :
    (functorEquiv B D).symm F = lift F := sorry

end functorEquiv

end CategoryTheory.Bicategory.HomotopyCategory
