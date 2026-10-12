/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Connected.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.7.2

The source statement is the global-continuity specialization of Mathlib's stronger
subset-continuity theorem.
-/

/- Lemma 5.7.2: continuous images of connected subsets are connected. -/
@[stacks 0376]
#check @IsConnected.image
