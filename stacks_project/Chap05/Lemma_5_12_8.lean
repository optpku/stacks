/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Compactness.ClosedPoints
import StacksCheckRecall

@[expose] public section

/- Lemma 5.12.8: every nonempty quasi-compact Kolmogorov space has a closed point. -/
@[stacks 005E]
#check @CompactSpace.exists_closedPoint
