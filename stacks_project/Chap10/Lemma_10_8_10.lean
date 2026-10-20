module

public import ReasLib.CategoryTheory.Filtered.Exact
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.8.10
@stack 04B0

The source hypothesis is kept explicitly: span cocones give common successors, while
postcomposition equalizers make every connected component filtered.  Exactness of the resulting
abelian-group colimits is recorded at the canonical `HasExactColimitsOfShape` interface.
-/

@[stacks 04B0 "filtered connected-component criterion"]
#check @CategoryTheory.ConnectedComponents.component.isFiltered_of_postcomposition

@[stacks 04B0 "exact abelian-group colimits"]
#check @CategoryTheory.hasExactColimitsOfShape_addCommGrp_of_postcomposition

end
