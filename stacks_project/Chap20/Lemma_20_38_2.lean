module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Limit.Complex

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Complex

/- Lemma 20.38.2 (08BY): let `(F_n^•)` be an inverse system of complexes of `𝒪_X`-modules and
let `𝓑` be a basis of opens. If the degree towers in degrees `m - 2` and `m - 1`, and the
cohomology tower in degree `m - 1`, have vanishing `R¹ lim` on `𝓑`, while the degree-`m`
cohomology tower is constant after `n₀`, then both canonical maps
`H^m(lim F) ⟶ lim H^m(F) ⟶ H^m(F_{n₀})` are isomorphisms. -/
@[stacks 08BY "comparison and eventual projection for a complex limit"]
#check @Comparison.andProjection_isIso

@[stacks 08BY "cohomology tower"]
#check @homologyFunctor
@[stacks 08BY "homology inverse tower"]
#check @homologyTower
@[stacks 08BY "degree tower"]
#check @Degree.tower
@[stacks 08BY "degree R¹-vanishing condition"]
#check @Degree.R1Vanishing
@[stacks 08BY "degree R¹-vanishing at a basis open"]
#check @Degree.R1Vanishing.at
@[stacks 08BY "cohomology tower"]
#check @Cohomology.tower
@[stacks 08BY "cohomology R¹-vanishing condition"]
#check @Cohomology.R1Vanishing
@[stacks 08BY "cohomology R¹-vanishing at a basis open"]
#check @Cohomology.R1Vanishing.at
@[stacks 08BY "eventually constant cohomology tower"]
#check @Cohomology.EventuallyConstant
@[stacks 08BY "transition map of an eventually constant tower"]
#check @Cohomology.EventuallyConstant.transitionMap
@[stacks 08BY "comparison map from limit cohomology"]
#check @comparison
@[stacks 08BY "eventual projection map"]
#check @projection
@[stacks 08BY "underlying comparison and limit projection"]
#check @Underlying.comparison_comp_preservesLimitIso
@[stacks 08BY "underlying limit projection"]
#check @Underlying.preservesLimitIso_hom_comp_π
@[stacks 08BY "comparison isomorphism"]
#check @Comparison.isIso
@[stacks 08BY "eventual projection isomorphism"]
#check @Projection.isIso
@[stacks 08BY "comparison followed by projection"]
#check @Comparison.compProjection_isIso
@[stacks 08BY "underlying sheaf preserves limits of shape"]
#check @AlgebraicGeometry.RingedSpace.moduleUnderlyingSheaf_preservesLimitsOfShape

end
