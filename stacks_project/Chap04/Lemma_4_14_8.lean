module

public import ReasLib.CategoryTheory.Limits.ChangeOfIndex
import StacksCheckRecall

@[expose] public section

universe vI uI vJ uJ vC uC

namespace CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable {H : I ⥤ J}
variable {M : I ⥤ C} [HasColimit M]
variable {N : J ⥤ C} [HasColimit N]
variable (t : M ⟶ H ⋙ N)

/- Lemma 4.14.8: a transformation `M ⟶ H ⋙ N` induces a unique comparison
`colimit M ⟶ colimit N` with the prescribed coprojection composites. -/
@[stacks 002K]
#check (colimitComparison.existsUnique t :
  ∃! θ : colimit M ⟶ colimit N,
    ∀ i : I, colimit.ι M i ≫ θ = t.app i ≫ colimit.ι N (H.obj i))

end CategoryTheory.Limits
