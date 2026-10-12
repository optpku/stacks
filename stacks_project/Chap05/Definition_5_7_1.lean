/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.ConnectedComponents.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 5.7.1

The canonical connected-component owner is Mathlib's `connectedComponent`; its maximal-subset
presentation is provided by `ReasLib.Topology.ConnectedComponents.Basic`.
-/

/- Definition 5.7.1 (1): connected spaces use Mathlib's canonical class. -/
@[stacks 004S "connected topological spaces"]
#check @ConnectedSpace

/- Definition 5.7.1 (1): the clopen characterization is Mathlib's canonical equivalence. -/
@[stacks 004S "connected spaces via clopen subsets"]
#check @connectedSpace_iff_clopen

/- Definition 5.7.1 (2): the point-indexed connected-component owner. -/
@[stacks 004S "connected components"]
#check @connectedComponent

/- Definition 5.7.1 (2): the equivalent maximal connected-subset presentation. -/
@[stacks 004S "connected components as maximal connected subsets"]
#check @maximal_isConnected_iff_eq_connectedComponent
