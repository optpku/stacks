/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict laws for horizontal composition of natural transformations

Horizontal composition in `Cat` is strictly associative, and identity transformations on
identity functors are strict units.
-/

@[expose] public section

universe vA uA vB uB vC uC vD uD

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- Lemma 4.28.2 (2) (Stacks 003F): horizontal composition of natural transformations is
strictly associative. -/
@[stacks 003F "horizontal composition is strictly associative"]
theorem NatTrans.hcomp_assoc
    {F₁ F₂ : A ⥤ B} {G₁ G₂ : B ⥤ C} {H₁ H₂ : C ⥤ D}
    (t : F₁ ⟶ F₂) (s : G₁ ⟶ G₂) (r : H₁ ⟶ H₂) :
    (t ◫ s) ◫ r = t ◫ (s ◫ r) := sorry

/-- Lemma 4.28.2 (5) (Stacks 003F): the identity transformation of an identity functor is a left
unit for horizontal composition. -/
@[stacks 003F "identity of the identity functor is a left horizontal unit", simp]
theorem NatTrans.id_hcomp {F₁ F₂ : A ⥤ B} (t : F₁ ⟶ F₂) :
    𝟙 (𝟭 A) ◫ t = t := sorry

/-- Lemma 4.28.2 (6) (Stacks 003F): the identity transformation of an identity functor is a right
unit for horizontal composition. -/
@[stacks 003F "identity of the identity functor is a right horizontal unit", simp]
theorem NatTrans.hcomp_id {F₁ F₂ : A ⥤ B} (t : F₁ ⟶ F₂) :
    t ◫ 𝟙 (𝟭 B) = t := sorry

end CategoryTheory
