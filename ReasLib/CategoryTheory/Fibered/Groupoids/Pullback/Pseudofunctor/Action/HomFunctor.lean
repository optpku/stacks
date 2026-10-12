/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Pullback.Pseudofunctor.Action.Construction

/-!
# Hom-functor computations for fixed-base pullback in groupoids

This leaf identifies both hom-functor actions with the direct `map` and `map₂` owners.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Pullback

open CategoryTheory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (u : C ⥤ D)

/-- The object action of the groupoid-fibred pullback hom functor is `map`. -/
@[simp]
theorem mapFunctor.obj
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D} (F : X ⟶ Y) :
    (mapFunctor u X Y).obj F = map u F := sorry

/-- The morphism action of the groupoid-fibred pullback hom functor is `map₂`. -/
@[simp]
theorem mapFunctor.map
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (mapFunctor u X Y).map eta = map₂ u eta := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.Pullback

