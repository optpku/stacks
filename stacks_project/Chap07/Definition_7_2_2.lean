module

public import Mathlib.CategoryTheory.Opposites
import StacksCheckRecall

@[expose] public section

universe vC uC vA uA

namespace CategoryTheory

section

variable (C : Type uC) [Category.{vC} C] (A : Type uA) [Category.{vA} A]

/- Definition 7.2.2 (1): a presheaf on `C` with values in `A` is a contravariant functor
from `C` to `A`, i.e. an object of type `Cᵒᵖ ⥤ A`. -/
@[stacks 00V3 "(1)"]
#check (Cᵒᵖ ⥤ A)

variable (F G : Cᵒᵖ ⥤ A)

/- Definition 7.2.2 (2): a morphism of `A`-valued presheaves on `C` is a transformation of
functors, i.e. a natural transformation `NatTrans F G`. -/
@[stacks 00V3 "(2)"]
#check (NatTrans F G)

/- Unspecialized owners of the two clauses above. -/
#check Functor
#check NatTrans

end

end CategoryTheory
