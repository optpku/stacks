/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Homological Functors Valued in an Abelian Full Subcategory

A homological functor whose values satisfy an object property lifts canonically to the associated
full subcategory.  When that full subcategory is abelian, faithfulness of its inclusion reflects
the exactness needed to make the lifted functor homological.
-/

universe uC vC uA vA

namespace CategoryTheory.ObjectProperty.FullSubcategory

open Limits

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
  [Pretriangulated C]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [Abelian P.FullSubcategory]
variable (F : C ⥤ A) [F.IsHomological] (hF : ∀ X, P (F.obj X))

/-- A homological functor landing in an abelian full subcategory remains homological after the
canonical `ObjectProperty.lift`. -/
@[stacks 0754 "homological lift to an abelian full subcategory"]
instance liftIsHomological : (P.lift F hF).IsHomological := sorry

end CategoryTheory.ObjectProperty.FullSubcategory
