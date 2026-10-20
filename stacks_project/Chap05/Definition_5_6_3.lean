/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Maps.Strict.Basic
import StacksCheckRecall

@[expose] public section

/- Mathlib's `Topology.IsStrictMap` is exactly the source's quotient-map condition on
`Set.rangeFactorization f`, while `Topology.isQuotientMap_iff_isStrictMap_surjective` identifies
submersive maps with quotient maps. The canonical predicates are stated for arbitrary maps rather
than taking continuity as a separate hypothesis: strictness supplies continuity through
`Topology.IsStrictMap.continuous`, so specializing to the source's continuous map recovers both
definitions. Using these owners avoids a parallel predicate and makes the established strict-
and quotient-map APIs available downstream. -/

/- Definition 5.6.3 (1): a continuous map is strict when its range factorization is a quotient
map; this is the canonical predicate `Topology.IsStrictMap`. -/
@[stacks 0406 "strict maps via the quotient-map range factorization"]
#check Topology.IsStrictMap

/- Definition 5.6.3 (2): the canonical owner for a submersive map is
`Topology.IsQuotientMap`. -/
@[stacks 0406 "submersive maps as quotient maps"]
#check Topology.IsQuotientMap

/- Companion check: a map is a quotient map exactly when it is strict and surjective, recovering
the source formulation of submersiveness. -/
@[stacks 0406 "submersive maps as strict surjections"]
#check Topology.isQuotientMap_iff_isStrictMap_surjective
