module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Limit.Truncation

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.DerivedCategory.Truncation
open AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Truncation

/- Lemma 20.37.9 (0D64): a single natural-number bound for `H^p(U, H^q(E))` on a topological
basis, uniformly for all `q < 0`, makes every compatible map from `E` to a derived limit of its
lower truncation tower an isomorphism. -/
@[stacks 0D64 "uniform basiswise negative vanishing makes the truncation comparison invertible"]
#check @Comparison.isIso_of_basisNegative

@[stacks 0D64 "uniform basiswise negative vanishing condition"]
#check @Basis.Negative
@[stacks 0D64 "uniform basiswise negative vanishing implies local vanishing"]
#check @Basis.Negative.toLocal

end
