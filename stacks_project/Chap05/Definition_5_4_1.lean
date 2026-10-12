/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.SeparatedMap
import StacksCheckRecall

@[expose] public section


/-
The source-facing notion is a property of an existing map, so `IsSeparatedMap` is the canonical
owner rather than a new bundled map or project-local predicate. Among its equivalent views,
`isSeparatedMap_iff_isClosedMap` matches the source's closed-map formulation for the canonical
diagonal `toPullbackDiag f`; `isSeparatedMap_iff_isClosed_diagonal` instead speaks about its range.
Mathlib's owner and bridge need only the topology on the source, so they are strictly stronger
than the source presentation with an additional continuity hypothesis.
-/

/- Canonical owner for fiberwise separation of an arbitrary function. -/
@[stacks 0CY1 "separated maps"]
#check IsSeparatedMap

/- `isSeparatedMap_iff_isClosedMap` identifies the canonical separated-map
predicate with closedness of the diagonal map `toPullbackDiag f : X → X ×_Y X`, exactly as in
the source definition. -/
@[stacks 0CY1 "separated maps via their closed diagonal"]
#check isSeparatedMap_iff_isClosedMap
