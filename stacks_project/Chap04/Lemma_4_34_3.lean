module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
public import ReasLib.CategoryTheory.Fibered.Inertia.Square.Bilimit.Construction

@[expose] public section

universe u v

namespace CategoryTheory
namespace FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, max u v, v} C}
variable (F : X ⟶ Y)

/- Lemma 4.34.3: the relative-inertia square is a `2`-fibre product in `Cat/C`.  The bilimit
statement is universe-polymorphic inside one homogeneous ambient `BasedCategory` bicategory. -/
@[stacks 04Z6]
#check (BasedCategory.RelativeInertia.Square.cone.isBilimit (toBasedFunctor F) :
  (BasedCategory.RelativeInertia.Square.cone (toBasedFunctor F)).IsBilimit)

end FiberedCategoryOver
end CategoryTheory
