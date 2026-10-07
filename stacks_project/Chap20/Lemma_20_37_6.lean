module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Limit.Truncation

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.DerivedCategory.Truncation
open AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Truncation

/- Lemma 20.37.6 (0D62): if, near every point, `H^p(U, H^(m-p)(E))` eventually vanishes
with a point- and degree-dependent bound, then every compatible map from `E` to a derived limit
of its lower truncation tower is an isomorphism. -/
@[stacks 0D62 "local eventual vanishing makes the lower-truncation comparison invertible"]
#check @Comparison.isIso_of_locallyEventual

#check @openCohomology
#check @openCohomology_forget
#check @LocallyEventual
#check @LocallyEventual.existsShrink
#check @Lower.Comparison.Exists

end
