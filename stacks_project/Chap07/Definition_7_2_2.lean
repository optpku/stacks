module

import ReasLib.CategoryTheory.Presheaf.Basic
import StacksCheckRecall

@[expose] public section

universe vC uC vA uA

namespace CategoryTheory

section

variable (C : Type uC) [Category.{vC} C] (A : Type uA) [Category.{vA} A]

/- Definition 7.2.2 (1): a presheaf on `C` with values in `A` is a contravariant functor
from `C` to `A`, i.e. an object of type `Cᵒᵖ ⥤ A`. -/
@[stacks 00V3]
#check (CategoryTheory.PresheafWithValues C A : Type (max (max vC vA) (max uC uA)))

variable (F G : PresheafWithValues C A)

/- Definition 7.2.2 (2): a morphism of `A`-valued presheaves on `C` is a transformation of
functors, i.e. a natural transformation `NatTrans F G`. -/
@[stacks 00V3 "(2)"]
#check (CategoryTheory.PresheafWithValues.Hom F G : Type (max uC vA))

end

end CategoryTheory
