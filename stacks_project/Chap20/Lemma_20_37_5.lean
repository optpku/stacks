module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Limit.StageComparison

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.Limit

/-
Lemma 20.37.5: if the local Milnor `R¹ lim` term vanishes after arbitrary neighborhood
shrinkings and the cohomology transition maps into a fixed stage are eventually injective, then
the canonical map from the derived limit to that stage is injective on the chosen cohomology
stalk.  The canonical stage projection is owned by `IsDerivedLimit`; no product presentation is
exposed in the chapter statement.
-/

@[stacks 0D61 "Lemma 20.37.5: injectivity of a derived-limit stage map on a cohomology stalk"]
#check @stageProjection_stalkInjective

@[stacks 0D61 "categorical stalk form of Lemma 20.37.5"]
#check @stageProjection_stalkMono

@[stacks 0D61 "cohomology tower for the stage comparison"]
#check @cohomologyTower
@[stacks 0D61 "local Milnor conditions"]
#check @LocalMilnorConditions
@[stacks 0D61 "cohomology stage map"]
#check @cohomologyStageMap
@[stacks 0D61 "cohomology stage map stalk monomorphism"]
#check @cohomologyStageMap_stalkMono

end
