/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pullback.Map.TwoCell

/-!
# Hom functor for pullback of fibred categories
-/

@[expose] public section

noncomputable section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

namespace FiberedCategoryOver.Pullback

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (u : C ⥤ D)

/-- For fixed `u`, pullback acts functorially on each hom category of fibred categories. -/
noncomputable def mapFunctor
    (X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D) :
    (X ⟶ Y) ⥤
      (FiberedCategoryOver.pullback u X ⟶ FiberedCategoryOver.pullback u Y) where
  obj := mapCanonical u
  map := map₂ u
  map_id := map₂.id u
  map_comp := map₂.comp u

/-- The object action of the pullback hom functor is `mapCanonical`. -/
@[simp]
theorem mapFunctor.obj
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D} (F : X ⟶ Y) :
    (mapFunctor u X Y).obj F = mapCanonical u F := sorry

/-- The morphism action of the pullback hom functor is pullback on `2`-cells. -/
@[simp]
theorem mapFunctor.map
    {X Y : FiberedCategoryOver.{uD, vD, w₀, w₁} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (mapFunctor u X Y).map eta = map₂ u eta := sorry

end FiberedCategoryOver.Pullback

end CategoryTheory
