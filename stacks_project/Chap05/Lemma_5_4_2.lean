/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.SeparatedMap
import StacksCheckRecall

@[expose] public section

/-
The source's neighborhood condition is definitionally `IsSeparatedMap f`, while
`isSeparatedMap_iff_isClosed_diagonal` identifies that predicate with closedness of
`f.pullbackDiagonal` in `X ×_Y X`. Thus the canonical theorem simultaneously recovers all three
source formulations. The canonical theorem has no continuity premise, so the tagged check is the
appropriate source-facing surface.
-/

/- Canonical owner theorem: a map is separated exactly when its pullback diagonal is closed. -/
@[stacks 0CY2 "closed diagonal and disjoint-neighborhood criteria for separated maps"]
#check isSeparatedMap_iff_isClosed_diagonal
