module

public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Diagram
import StacksCheckRecall

@[expose] public section

universe vI uI vC uC vD uD

namespace CategoryTheory

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {M : I ⥤ C} (F : C ⥤ D)
variable (hFiltered : IsFiltered.IsEssentiallyConstant M)
variable (hCofiltered : IsCofiltered.IsEssentiallyConstant M)

/-
The source needs the filtered and cofiltered postcomposition implications. Mathlib's verified
`Functor.IsEventuallyConstantFrom` and `Functor.IsEventuallyConstantTo` candidates are stronger:
they require all transition maps from or to one stage to be isomorphisms, so they do not express
the Stacks cocone/cone factorization predicates. The chapter owners below match both implications,
and tagged recalls, as in nearby Chap04 exact-owner files, avoid duplicate wrapper lemmas. Their
only generalization is to omit `[IsFiltered I]` and `[IsCofiltered I]`, which the predicates and
implications do not use; specialization to the source index categories recovers the two clauses.
Keeping that boundary in the owners lets downstream code postcompose without rebuilding irrelevant
index-category instances.
-/

/- Lemma 4.22.8: postcomposition with a functor preserves essential constancy of filtered
diagrams. The canonical owner theorem lives in `Definition_4_22_2`. -/
@[stacks 05SH "postcomposition preserves filtered essential constancy"]
#check (IsFiltered.IsEssentiallyConstant.map hFiltered F :
  IsFiltered.IsEssentiallyConstant (M ⋙ F))

/- Lemma 4.22.8, dual form: postcomposition with a functor preserves essential constancy of
cofiltered diagrams. The canonical owner theorem lives in `Definition_4_22_2`. -/
@[stacks 05SH "postcomposition preserves cofiltered essential constancy"]
#check (IsCofiltered.IsEssentiallyConstant.map hCofiltered F :
  IsCofiltered.IsEssentiallyConstant (M ⋙ F))

end CategoryTheory
