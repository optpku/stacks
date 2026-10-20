/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Connected.TotallyDisconnected
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.7.9

The connected-components quotient and its universal factorization are owned by Mathlib.
-/

/- Lemma 5.7.9 (1): the connected-components quotient is totally disconnected. -/
@[stacks 08ZL "the connected-components quotient is totally disconnected"]
#check @ConnectedComponents.totallyDisconnectedSpace

/- Lemma 5.7.9 (2): the canonical continuous factorization through connected components. -/
@[stacks 08ZL "continuous factorization through connected components"]
#check @Continuous.connectedComponentsLift

/- Lemma 5.7.9 (2): the canonical factorization equation. -/
@[stacks 08ZL "continuous factorization through connected components"]
#check @Continuous.connectedComponentsLift_comp_coe

/- Lemma 5.7.9 (2): uniqueness of the canonical factorization. -/
@[stacks 08ZL "continuous factorization through connected components"]
#check @Continuous.connectedComponentsLift_unique
