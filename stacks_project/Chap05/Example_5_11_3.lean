/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.KrullDimension.TailInterval
import StacksCheckRecall

@[expose] public section

/-!
# Example 5.11.3

The tail-topology interval is reusable Krull-dimension infrastructure.  Its
topology data, Noetherian instance, and endpoint codimension API are owned by
`ReasLib.Topology.KrullDimension.TailInterval`.
-/

/- The explicit carrier and its canonical topology are available downstream. -/
#check @TailTopologyUnitInterval
#check @TailTopologyUnitInterval.topology

/- Example 5.11.3 (1): positive-index tails generate the topology. -/
@[stacks 02I5 "tail-topology unit interval"]
#check @TailTopologyUnitInterval.openTail

/- Example 5.11.3 (2): open sets are empty, whole, or tails. -/
@[stacks 02I5 "classification of the open sets"]
#check @TailTopologyUnitInterval.isOpen_iff

/- Example 5.11.3 (3): closed sets have the stated initial-interval classification. -/
@[stacks 02I5 "classification of the closed sets"]
#check @TailTopologyUnitInterval.isClosed_iff

/- Example 5.11.3 (4): the tail-topology interval is Noetherian. -/
@[stacks 02I5 "Noetherianity of the tail topology"]
#check (inferInstance : TopologicalSpace.NoetherianSpace TailTopologyUnitInterval)

/- Example 5.11.3 (5): the displayed proper closed initial intervals are irreducible. -/
@[stacks 02I5 "irreducibility of the proper closed initial intervals"]
#check @TailTopologyUnitInterval.closedInitial_isIrreducible

/- Example 5.11.3 (6): the endpoint `{0}` is an irreducible closed subset. -/
@[stacks 02I5 "the irreducible closed subset Y = {0}"]
#check @TailTopologyUnitInterval.zeroIrreducibleClosed

/- Example 5.11.3 (7): that endpoint has infinite codimension. -/
@[stacks 02I5 "infinite codimension of Y = {0}"]
#check @TailTopologyUnitInterval.zero_codimension_eq_top
