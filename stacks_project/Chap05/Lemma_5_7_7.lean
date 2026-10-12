/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.ConnectedComponents.FiniteFibers
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.7.7

The finite-fiber component API is owned by
`ReasLib.Topology.ConnectedComponents.FiniteFibers`.
-/

/- Lemma 5.7.7 (1): a finite fiber bounds the number of connected components. -/
@[stacks 07VB "bound on the number of connected components"]
#check @IsOpenMap.natCard_connectedComponents_le_ncard_preimage_singleton

/- Lemma 5.7.7 (2): source connected components are clopen. -/
@[stacks 07VB "connected components are clopen"]
#check @IsOpenMap.isClopen_connectedComponent_of_finiteFiber

/- Lemma 5.7.7 (3): component images are nonempty and clopen. -/
@[stacks 07VB "component images are nonempty and clopen"]
#check @IsOpenMap.image_connectedComponent_nonempty_and_isClopen_of_finiteFiber

/- Lemma 5.7.7 (4): every source component maps onto the target. -/
@[stacks 07VB "every component maps onto the connected target"]
#check @IsOpenMap.image_connectedComponent_eq_univ_of_finiteFiber
