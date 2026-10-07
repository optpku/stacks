module

public import Mathlib.CategoryTheory.Filtered.Final
import StacksCheckRecall

@[expose] public section


universe v u

namespace CategoryTheory
namespace ObjectProperty

variable {I : Type u} [Category.{v} I]
variable (P : ObjectProperty I)
variable [IsFiltered I]
variable (h : ∀ X : I, ∃ Y : P.FullSubcategory, Nonempty (X ⟶ Y.obj))

/- The source full subcategory is represented by `P.FullSubcategory` with inclusion `P.ι`.
The verified owners `IsFiltered.of_exists_of_isFiltered_of_fullyFaithful` and
`Functor.final_of_exists_of_isFiltered_of_fullyFaithful` apply because `P.ι` has the canonical
full and faithful instances and `h` is exactly their object-reachability hypothesis. The latter
owner is stronger in allowing `IsFilteredOrEmpty I`, but this specialization retains the source
assumption `IsFiltered I`. Separate tagged checks expose the two independent conclusions without
parallel wrapper theorems and keep the generic owner API available downstream. -/

/- Lemma 4.19.3 (1): a full subcategory reached by a morphism from every object of the filtered
ambient category is filtered. -/
@[stacks 0BUC "the full subcategory is filtered"]
#check
  (IsFiltered.of_exists_of_isFiltered_of_fullyFaithful P.ι h :
    IsFiltered P.FullSubcategory)

/- Lemma 4.19.3 (2): under the same reachability hypothesis, the full-subcategory inclusion is
final, which is the mathlib terminology for cofinal. -/
@[stacks 0BUC "the full-subcategory inclusion is final (cofinal)"]
#check
  (Functor.final_of_exists_of_isFiltered_of_fullyFaithful P.ι h :
    P.ι.Final)

end ObjectProperty
end CategoryTheory
