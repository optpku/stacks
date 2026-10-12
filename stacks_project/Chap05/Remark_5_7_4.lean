/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.ConnectedComponents.ClopenCounterexample
import StacksCheckRecall

@[expose] public section

open Topology.ConnectedComponents.ClopenCounterexample

/- Remark 5.7.4 (1): every connected component lies in the intersection of
the clopen neighborhoods of its point. -/
@[stacks 0FIY "connected components lie in every clopen neighborhood"]
#check @connectedComponent_subset_iInter_isClopen

/- Remark 5.7.4 (2): the counterexample's connected component is explicit. -/
@[stacks 0FIY "the connected component of x in the explicit space"]
#check connectedComponent_x

/- Remark 5.7.4 (3): its clopen-neighborhood intersection is explicit. -/
@[stacks 0FIY "the clopen-neighborhood intersection of x in the explicit space"]
#check iInter_isClopen_x

/- Remark 5.7.4 (4): the canonical inclusion is strict in this space. -/
@[stacks 0FIY "strictness of the clopen-neighborhood inclusion"]
#check connectedComponent_x_ssubset_iInter_isClopen
