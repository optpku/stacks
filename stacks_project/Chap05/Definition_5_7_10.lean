/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Connected.LocallyConnected
import StacksCheckRecall

@[expose] public section

/-
`LocallyConnectedSpace` is mathlib's canonical owner for local connectedness, and
`locallyConnectedSpace_iff_hasBasis_isOpen_isConnected` is its source-facing neighborhood-basis
view. Recalling both keeps the instance-driven API available downstream while avoiding a parallel
predicate or theorem for the same notion.
-/

/- Definition 5.7.10: a topological space is locally connected when every point has a fundamental
system of connected neighborhoods; this is the canonical class `LocallyConnectedSpace`. -/
@[stacks 04MD "locally connected spaces via connected neighborhood bases"]
#check @LocallyConnectedSpace

/- The source's fundamental-system formulation is the canonical equivalence with bases of open
connected neighborhoods. -/
#check @locallyConnectedSpace_iff_hasBasis_isOpen_isConnected
