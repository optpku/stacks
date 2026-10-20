module

public import ReasLib.CategoryTheory.RepresentablePresheaf.Elements
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open scoped RepresentablePresheaf

universe v u

variable {C : Type u} [Category.{v} C]
variable (X : C)

/- Example 4.38.7: the opposite category of elements of a representable presheaf is canonically
equivalent over the base to the corresponding slice category. -/
@[stacks 0044]
#check (RepresentablePresheaf.Elements.overEquivalence X :
  h[X].Elementsᵒᵖ ≌ Over X)

end CategoryTheory
