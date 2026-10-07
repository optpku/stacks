module

public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Final
import StacksCheckRecall

@[expose] public section

universe vI uI vJ uJ vC uC

namespace CategoryTheory

variable {I : Type uI} [Category.{vI} I] [IsFiltered I]
variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable (H : I ⥤ J) [H.Final] (M : J ⥤ C)

/- Lemma 4.22.11: essential constancy of a filtered diagram is invariant under restriction along
a final functor. -/
@[stacks 0A1S]
#check (IsFiltered.IsEssentiallyConstant.iff_comp_final H M :
  IsFiltered.IsEssentiallyConstant M ↔ IsFiltered.IsEssentiallyConstant (H ⋙ M))

/- The neutral support module also exposes the dual initial-functor statement. -/
#check CategoryTheory.IsCofiltered.IsEssentiallyConstant.iff_comp_initial

end CategoryTheory
