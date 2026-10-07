module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Bicategory
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
public import ReasLib.CategoryTheory.Fibered.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of fibred-category projections

The projection of a fibred category may be postcomposed with any fibred
functor.  This changes the base without choosing a cleavage or an indexed
presentation.
-/

@[expose] public section

universe uA uB uC vA vB vC

namespace CategoryTheory.FiberedCategoryOver

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]

/-- Postcompose the projection of a fibred category with another fibred
functor. -/
@[stacks 09WV "composition of fibred-category projections"]
def comp
    (X : FiberedCategoryOver.{uB, vB, uA, vA} B)
    (G : B ⥤ C) [G.IsFibered] :
    FiberedCategoryOver.{uC, vC, uA, vA} C :=
  ofFunctor (X.p ⋙ G)

namespace comp

/-- A morphism of fibred categories over `B` commutes with the projections
after both projections are postcomposed with a fibred functor `G : B ⥤ C`. -/
@[stacks 09WV "morphism of composite fibred-category projections"]
theorem map_comm
    {X Y : FiberedCategoryOver.{uB, vB, uA, vA} B}
    (F : X ⟶ Y) (G : B ⥤ C) [G.IsFibered] :
    FiberedCategoryOver.toFunctor F ⋙ (Y.comp G).p = (X.comp G).p := sorry

end comp

/-- The projection of `X.comp G` is the composite projection. -/
@[simp, stacks 09WV "composite projection"]
theorem comp_p
    (X : FiberedCategoryOver.{uB, vB, uA, vA} B)
    (G : B ⥤ C) [G.IsFibered] :
    (X.comp G).p = X.p ⋙ G := sorry

/-- Composing the projection does not change the total category. -/
@[simp, stacks 09WV "composite total category"]
theorem comp_total
    (X : FiberedCategoryOver.{uB, vB, uA, vA} B)
    (G : B ⥤ C) [G.IsFibered] :
    (X.comp G).total = X.total := sorry

end CategoryTheory.FiberedCategoryOver
