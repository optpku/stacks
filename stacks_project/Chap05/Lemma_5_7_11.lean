/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Connected.LocallyConnected
import StacksCheckRecall

@[expose] public section

/-
The four source consequences are already the canonical API of `LocallyConnectedSpace`:
`IsOpen.locallyConnectedSpace`, `isOpen_connectedComponent`, `IsOpen.connectedComponentIn`, and
`LocallyConnectedSpace.open_connected_basis`. For a point of an open set, the identity
`connectedComponentIn_eq_image` identifies the third formulation with the image in the ambient
space of the corresponding subtype component, so its ambient openness is precisely the source's
claim about components of open subsets. Direct recalls retain exactly the source assumption and
make the owner namespaces and instances available downstream without a parallel predicate,
subtype wrapper, or stronger ambient hypothesis.
-/

/- Lemma 5.7.11 (1): open subsets of a locally connected space are locally connected.
This is exactly the canonical theorem `IsOpen.locallyConnectedSpace`. -/
@[stacks 04ME "open subsets remain locally connected"]
#check @IsOpen.locallyConnectedSpace

/- Lemma 5.7.11 (2): in a locally connected space, connected components are open.
This is exactly the canonical theorem `isOpen_connectedComponent`. -/
@[stacks 04ME "connected components of the ambient space are open"]
#check @isOpen_connectedComponent

/- Lemma 5.7.11 (3): for an open subset `U`, `connectedComponentIn U x` is open.
This is exactly the canonical theorem `IsOpen.connectedComponentIn`. -/
@[stacks 04ME "connected components inside open subsets are open"]
#check @IsOpen.connectedComponentIn

/- Lemma 5.7.11 (4): every point of a locally connected space has a neighbourhood basis of open
connected sets. This is exactly the canonical theorem
`LocallyConnectedSpace.open_connected_basis`. -/
@[stacks 04ME "points have bases of open connected neighborhoods"]
#check @LocallyConnectedSpace.open_connected_basis
