/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Limit.ComplexComparison
import StacksCheckRecall

@[expose] public section

/-
Lemma 21.24.2 (08CT): for a sequential inverse system `F` of complexes of modules on a ringed
site, basiswise vanishing of the three relevant `R¹ lim` terms makes the cohomology comparison
`H^m(lim F) ⟶ lim H^m(F)` an isomorphism.  If the degree-`m` cohomology towers are eventually
constant from `n₀`, the projection `lim H^m(F) ⟶ H^m(F.obj (op n₀))` is also an isomorphism.

The reusable maps and theorem bundle are owned by
`RingedSite.Hom.ModuleSections.Limit`; the longer names below are compatibility entries for older
chapter consumers.
-/

@[stacks 08CT]
#check @RingedSite.Hom.ModuleSections.Limit.comparison_and_projection_isIso

#check @RingedSite.Hom.ModuleSections.Limit.comparison
#check @RingedSite.Hom.ModuleSections.Limit.projection
#check @RingedSite.Hom.ModuleSections.Limit.comparison_app_bijective_of_basiswise_r1
#check @RingedSite.Hom.ModuleSections.Limit.comparison_isIso_of_basiswise_r1
#check @RingedSite.Hom.ModuleSections.Limit.cohomologyTower_isEventuallyConstantTo_of_transitionMap_isIso
#check @RingedSite.Hom.ModuleSections.Limit.cohomologyTower_transitionMap_isIso_of_isEventuallyConstantTo
#check @RingedSite.Hom.ModuleSections.Limit.projection_app_bijective_of_basiswise_eventuallyConstant
#check @RingedSite.Hom.ModuleSections.Limit.projection_isIso_of_basiswise_eventuallyConstant
#check @RingedSite.Hom.ModuleSections.Limit.projection_isIso_of_basiswise_eventuallyConstantTo

#check @RingedSite.Hom.cohomologySheafLimitComparison_app_bijective_of_basiswise_vanishing_r1lim
#check @RingedSite.Hom.cohomologySheafLimitComparison_isIso_of_basiswise_vanishing_r1lim
#check @RingedSite.Hom.complexSectionCohomologyInverseSystem_isEventuallyConstantTo_of_transitionMap_isIso
#check @RingedSite.Hom.complexSectionCohomologyInverseSystem_transitionMap_isIso_of_isEventuallyConstantTo
#check @RingedSite.Hom.cohomologySheafLimitProjection_app_bijective_of_basiswise_eventually_constant
#check @RingedSite.Hom.cohomologySheafLimitProjection_isIso_of_basiswise_eventually_constant
#check @RingedSite.Hom.cohomologySheafLimitProjection_isIso_of_basiswise_eventuallyConstantTo
#check @RingedSite.Hom.cohomologySheafLimitComparison_and_projection_isIso_of_basiswise_vanishing_r1lim
