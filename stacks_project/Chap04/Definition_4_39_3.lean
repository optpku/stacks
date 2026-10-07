module

public import ReasLib.CategoryTheory.Fibered.Setoids.Bicategory
import StacksCheckRecall

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

/- Definition 4.39.3 (1): an object is a based category whose projection is fibred in setoids. -/
@[stacks 02Y1 "(1)"]
#check (FiberedCategoryOver.Setoids.{u, v, w, vS} C :
  Type max (w + 1) (vS + 1) u v)

/- Definition 4.39.3 (2): `1`-morphisms are the inherited based functors over `C`. -/
@[stacks 02Y1 "(2)"]
#check (fun (X Y : FiberedCategoryOver.Setoids.{u, v, w, vS} C) ↦ (X ⟶ Y) :
  FiberedCategoryOver.Setoids.{u, v, w, vS} C →
    FiberedCategoryOver.Setoids.{u, v, w, vS} C → Type max w vS)

/- Definition 4.39.3 (3): `2`-morphisms are the inherited based natural transformations. -/
@[stacks 02Y1 "(3)"]
#check (fun {X Y : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    (F G : X ⟶ Y) ↦ (F ⟶ G) :
  {X Y : FiberedCategoryOver.Setoids.{u, v, w, vS} C} →
    (F G : X ⟶ Y) → Type max w vS)

end CategoryTheory
