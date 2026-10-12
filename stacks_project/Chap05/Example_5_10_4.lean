/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.KrullDimension.FiniteChain
public import ReasLib.Topology.Sierpinski
import StacksCheckRecall

@[expose] public section

/-!
# Example 5.10.4

The `Prop` model of the Sierpinski space and the finite Alexandrov-chain
dimension computation are reusable topology API.  The source entry only tracks
their four stated consequences.
-/

/- The explicit irreducible-closed endpoints are available as reusable data. -/
#check @Sierpinski.closedPoint
#check @Sierpinski.whole

/- Example 5.10.4 (1): the Sierpinski space has exactly three open subsets. -/
@[stacks 0057 "the three open subsets of the Sierpinski space"]
#check @Sierpinski.isOpen_iff

/- Example 5.10.4 (2): its closed-point-to-whole-space chain is maximal. -/
@[stacks 0057 "the maximal chain from the closed point to the whole space"]
#check @Sierpinski.irreducibleCloseds_isMaxChain

/- Example 5.10.4 (3): the Sierpinski space has topological Krull dimension one. -/
@[stacks 0057 "the Sierpinski space has Krull dimension one"]
#check @Sierpinski.topologicalKrullDim_eq_one

/- Example 5.10.4 (4): the finite upper-set Alexandrov chain has the prescribed dimension. -/
@[stacks 0057 "finite Alexandrov chains of arbitrary dimension"]
#check @Topology.WithUpperSet.topologicalKrullDim_fin_succ
