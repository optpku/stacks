module

public import ReasLib.Topology.Maps.Proper.QuasiProper
import StacksCheckRecall

@[expose] public section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y}

/- Definition 5.17.2 (1): closed maps use Mathlib's canonical predicate. -/
@[stacks 005O "closed maps carry closed subsets to closed subsets"]
#check IsClosedMap

/- Definition 5.17.2 (2): Bourbaki properness uses Mathlib's canonical
predicate. -/
@[stacks 005O "Bourbaki-proper maps are closed after arbitrary products"]
#check IsProperMap

/- Definition 5.17.2 (3): quasi-properness is owned by ReasLib. -/
@[stacks 005O "quasi-proper maps preserve compactness under inverse image"]
#check IsQuasiProperMap

/- Definition 5.17.2 (3): quasi-properness has its explicit conjunction API. -/
@[stacks 005O]
#check @isQuasiProperMap_iff

/- Definition 5.17.2 (3): proper maps are quasi-proper and closed. -/
@[stacks 005O]
#check @isProperMap_iff_isQuasiProperMap_and_isClosedMap

/- Definition 5.17.2 (4): proper maps have closed pullback projections. -/
@[stacks 005O "universally closed maps have closed pullback projections"]
#check @IsProperMap.isClosedMap_pullback_snd

/- Definition 5.17.2 (4): the pullback-projection condition characterizes
proper maps. -/
@[stacks 005O]
#check @isProperMap_iff_isClosedMap_pullback_snd

/- Definition 5.17.2 (5): a Stacks-proper map is separated and
Bourbaki-proper. -/
@[stacks 005O "proper maps are separated and universally closed"]
#check (fun f : X → Y ↦ IsSeparatedMap f ∧ IsProperMap f)
