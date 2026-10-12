/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Counterexamples.TwoClosedPoints.Sheaf
import StacksCheckRecall

/-!
# Two closed points counterexample

Direct import for the two-closed-points topological space and its parameterized tail-sheaf system.
Use `TopCat.Counterexample.TwoClosedPoints` for the topological API and its `Tail` namespace for
the parameterized sheaf system.
-/

@[expose] public section

/- The concrete topology is owned by `Basic`; the aggregate exposes the same stable owner names
   used by downstream counterexample proofs. -/
/- Stacks 01BT: counterexample space. -/
@[stacks 01BT "counterexample space"] #check TopCat.Counterexample.TwoClosedPoints.space

/- Stacks 01BT: filtered tail-sheaf diagram. -/
@[stacks 01BT "filtered tail-sheaf diagram"] #check TopCat.Counterexample.TwoClosedPoints.Tail.sheafFunctor

/- Stacks 01BT: global-sections comparison morphism. -/
@[stacks 01BT "global-sections comparison morphism"] #check TopCat.Counterexample.TwoClosedPoints.Tail.globalSectionsComparison

/- Stacks 01BT: failure of global-sections preservation. -/
@[stacks 01BT "failure of global-sections preservation"] #check TopCat.Counterexample.TwoClosedPoints.Tail.globalSectionsComparison_not_isIso_of_nontrivial
