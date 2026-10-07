module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Comparison.Equivalence
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Limits
open scoped Bicategory CategoricalPullback

universe v u

variable {C : Type u} [Category.{v} C]
variable {X Y Z : BasedCategory C}
variable (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) [Y.p.IsFibered]

/- Remark 4.35.8: the explicit same-fibre pseudo-pullback of morphisms fibred in groupoids is
canonically equivalent to the ordinary categorical pullback of their underlying functors. -/
@[stacks 0H2E]
#check (BasedCategory.PseudoPullback.Comparison.equivalence F G :
  (BasedCategory.PseudoPullback F G).obj ≌ F.toFunctor ⊡ G.toFunctor)

end CategoryTheory
