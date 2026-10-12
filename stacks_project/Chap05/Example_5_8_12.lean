/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Cofinite.Pointed
import StacksCheckRecall

@[expose] public section

/-!
# Example 5.8.12

The pointed cofinite construction is a reusable topology rather than a
chapter-local type synonym.  It is modelled by `WithTopology`, so its selected
topology cannot conflict with another topology on the underlying carrier.
-/

/- The explicit topology owner and its identity equivalence are available for later constructions. -/
#check @TopologicalSpace.pointedCofinite
#check @PointedCofiniteTopology.of
#check @PointedCofiniteTopology.punctured

/- Example 5.8.12 (1): closed sets are the whole space and the finite subsets avoiding the point. -/
@[stacks 0B35 "closed sets in the pointed cofinite topology"]
#check @PointedCofiniteTopology.isClosed_iff

/- Example 5.8.12 (2): pointed cofinite spaces are sober. -/
@[stacks 0B35 "the pointed cofinite topology is sober"]
#check @PointedCofiniteTopology.sober

/- Example 5.8.12 (3): puncturing an infinite pointed cofinite space is not quasi-sober. -/
@[stacks 0B35 "the punctured pointed cofinite topology is not quasi-sober"]
#check @PointedCofiniteTopology.punctured_not_quasiSober
