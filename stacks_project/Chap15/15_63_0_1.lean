module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.CohomologyProduct
import StacksCheckRecall

@[expose] public section

/-!
# Equation 15.64.0.1 (068H)

Repository source label: 15.63.0.1.

The chain-level and derived cohomology products are owned by
CategoryTheory.derivedCohomologyProduct and its supporting ReasLib declarations. This chapter
entry is only their source-facing recall.

@stack 068H
-/

/- The canonical derived cohomology product and its explicit tensor-model comparison. -/
@[stacks 068H "derived cohomology product"]
#check @CategoryTheory.derivedCohomologyProduct

#check @CategoryTheory.cycleTensorToComponent_d_eq_zero
#check @CategoryTheory.cochainCohomologyProduct
#check @CategoryTheory.preimageTensorIso

#print axioms CategoryTheory.cochainCohomologyProduct
#print axioms CategoryTheory.preimageTensorIso
#print axioms CategoryTheory.derivedCohomologyProduct
