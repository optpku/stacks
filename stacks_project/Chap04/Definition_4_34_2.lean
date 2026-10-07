module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Objects

@[expose] public section

universe u v w vS

namespace CategoryTheory

namespace FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}
variable (F : X ⟶ Y)

/- Definition 4.34.2 (1): for a morphism `F : X ⟶ Y` of categories fibred over `C`, relative
inertia is the fibred category `relativeInertia F`. -/
@[stacks 034I "(1) relative inertia"]
#check (relativeInertia F : FiberedCategoryOver.{u, v, max w vS, vS} C)

/- Definition 4.34.2 (2): absolute inertia is the same construction applied to the structure
morphism of a category fibred over `C`. -/
@[stacks 034I "(2) absolute inertia"]
#check (inertia X : FiberedCategoryOver.{u, v, max w vS, vS} C)

end FiberedCategoryOver

end CategoryTheory
