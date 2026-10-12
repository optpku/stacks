/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Category
public import ReasLib.CategoryTheory.DisplayedCategory.Transport

/-!
# Displayed category of Postnikov systems

This leaf presents finite Postnikov systems as displayed objects over their finite rows.  The
existing `PostnikovSystem.Morphism.changeBase` transport and its category-law API remain the
canonical owners of dependent equalities.
-/

@[expose] public section

open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.PostnikovSystem.Morphism

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The displayed category of finite Postnikov systems over `ComposableArrows D n`. -/
@[reducible, stacks 0D7Z "displayed category of finite Postnikov systems"]
def displayedCategory (D : Type u) [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
    (n : ℕ) :
    DisplayedCategory (ComposableArrows D n) where
  obj X := PostnikovSystem X
  Hom := fun {X Y} φ P P' => PostnikovSystem.Morphism P P' φ
  id := fun {X} P => PostnikovSystem.Morphism.id P
  comp := fun {X Y Z} {φ ψ} {P P' P''} m n =>
    PostnikovSystem.Morphism.comp m n
  id_comp := fun _ => sorry
  comp_id := fun _ => sorry
  assoc := fun _ _ _ => sorry

/-- The displayed-object family of `displayedCategory` is `PostnikovSystem`. -/
@[simp, stacks 0D7Z "displayed Postnikov-system objects"]
theorem displayedCategory_obj (n : ℕ) (X : ComposableArrows D n) :
    (displayedCategory D n).obj X = PostnikovSystem X := sorry

/-- The displayed hom family of `displayedCategory` is `PostnikovSystem.Morphism`. -/
@[simp, stacks 0D7Z "displayed Postnikov-system morphisms"]
theorem displayedCategory_hom (n : ℕ) {X Y : ComposableArrows D n} {φ : X ⟶ Y}
    (P : PostnikovSystem X) (P' : PostnikovSystem Y) :
    (displayedCategory D n).Hom φ P P' = PostnikovSystem.Morphism P P' φ := sorry

/-- The identity operation of `displayedCategory` is the canonical Postnikov-system identity. -/
@[simp, stacks 0D7Z "displayed Postnikov-system identity"]
theorem displayedCategory_id (n : ℕ) {X : ComposableArrows D n} (P : PostnikovSystem X) :
    (displayedCategory D n).id P = PostnikovSystem.Morphism.id P := sorry

/-- The composition operation of `displayedCategory` is the canonical Postnikov-system
composition. -/
@[simp, stacks 0D7Z "displayed Postnikov-system composition"]
theorem displayedCategory_comp (n : ℕ) {X Y Z : ComposableArrows D n}
    {φ : X ⟶ Y} {ψ : Y ⟶ Z}
    {P : PostnikovSystem X} {P' : PostnikovSystem Y} {P'' : PostnikovSystem Z}
    (m : PostnikovSystem.Morphism P P' φ)
    (n' : PostnikovSystem.Morphism P' P'' ψ) :
    (displayedCategory D n).comp m n' = PostnikovSystem.Morphism.comp m n' := sorry

/-- The canonical Postnikov-system base transport agrees with generic displayed transport. -/
@[simp, stacks 0D7Z "displayed Postnikov-system transport"]
theorem changeBase_eq_cast {n : ℕ} {X Y : ComposableArrows D n} {φ ψ : X ⟶ Y}
    {P : PostnikovSystem X} {P' : PostnikovSystem Y}
    (h : φ = ψ) (m : PostnikovSystem.Morphism P P' φ) :
    PostnikovSystem.Morphism.changeBase h m =
      DisplayedCategory.Hom.cast (displayedCategory D n) h m := sorry

/-- The generic displayed transport can be converted back to the owner-level Postnikov-system
transport. -/
@[stacks 0D7Z "owner-level transport of Postnikov-system morphisms"]
theorem cast_eq_changeBase {n : ℕ} {X Y : ComposableArrows D n} {φ ψ : X ⟶ Y}
    {P : PostnikovSystem X} {P' : PostnikovSystem Y}
    (h : φ = ψ) (m : PostnikovSystem.Morphism P P' φ) :
    DisplayedCategory.Hom.cast (displayedCategory D n) h m =
      PostnikovSystem.Morphism.changeBase h m :=
  (changeBase_eq_cast h m).symm

end CategoryTheory.PostnikovSystem.Morphism

end
