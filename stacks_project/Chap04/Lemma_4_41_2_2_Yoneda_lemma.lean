module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Yoneda.Equivalence
import StacksCheckRecall

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]
variable (p : S ⥤ C) [Functor.IsFibered.InGroupoids p] (U : C)

/- Lemma 4.41.2 (2-Yoneda lemma): evaluation on the full category
`Mor_{Cat/C}(C/U, S)` at `𝟙 U` is an equivalence with the fiber over `U`. -/
@[stacks 004B]
#check (BasedCategory.Yoneda.evaluation.isEquivalence p U :
  (BasedCategory.Yoneda.evaluation p U).IsEquivalence)

end CategoryTheory
