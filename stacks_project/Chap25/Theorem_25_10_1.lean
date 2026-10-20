module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.ColimitComparison
import StacksCheckRecall

/-!
# Cohomology and hypercoverings

The homotopy refinement category, its Cech cohomology diagram, the actual pointwise colimit
functor, and the comparison with objectwise sheaf cohomology are owned by
`ReasLib.CategoryTheory.Sites.Hypercovering.Cech`.
-/

open CategoryTheory

/- Theorem 25.10.1: for every object `X` of a site with pullbacks and every `i : ℕ`, there is
a refinement-natural comparison from hypercovering Cech cohomology to `H^i(X, -)` whose
induced map on the refinement colimit is an isomorphism. -/
@[stacks 01H0] #check @Hypercovering.Cech.comparison_nonempty

#check @Hypercovering.HomotopyCategory
#check @Hypercovering.RefinementCategory
#check @Hypercovering.refinementObject
#check @Hypercovering.refinementCategoryIsFiltered
#check @Hypercovering.Cech.refinementDiagram
#check @Hypercovering.Cech.cohomologyFunctor
#check @Hypercovering.Cech.stageMap
#check @Hypercovering.Cech.RefinementComparison
#check @Hypercovering.Cech.comparison
#check @Hypercovering.Cech.ι_comp_comparison
#check @Hypercovering.Cech.stageMap_comp_comparison_app
#check @Hypercovering.Cech.Comparison
#check @Hypercovering.Cech.Comparison.hom
#check @Hypercovering.Cech.Comparison.ι_comp_hom
#check @Hypercovering.Cech.isIsomorphic_objectwiseCohomology
