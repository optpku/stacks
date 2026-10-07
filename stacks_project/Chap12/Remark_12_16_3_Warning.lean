module

public import ReasLib.CategoryTheory.GradedObject.Total
public import ReasLib.Topology.Sheaves.Abelian.CountableProducts
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

/- Remark 12.16.3 (Warning) (1): the opposite of abelian sheaves on the real line has countable
coproducts which are not exact, so the total functor on integer-graded objects is not exact. -/
@[stacks 0AMH] #check
  GradedObject.not_exact_total_of_not_countableAB4
    ℤ ((TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ))ᵒᵖ)
      TopCat.Sheaf.realLineOpposite_not_countableAB4

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B : GradedObject ℤ C} (φ : A ⟶ B) (i : ℤ)

/- Remark 12.16.3 (Warning) (2): the kernel of a morphism of graded objects is computed
degreewise.  Formally, evaluation carries the chosen kernel to a kernel of the component map. -/
#check
  (inferInstance :
    IsIso (kernelComparison φ (GradedObject.eval i : GradedObject ℤ C ⥤ C)))

end CategoryTheory
