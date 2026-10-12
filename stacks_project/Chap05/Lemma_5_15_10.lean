/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Constructible.Retrocompact
import StacksCheckRecall

@[expose] public section

/- Lemma 5.15.10: every constructible subset is retrocompact. -/
@[stacks 09YH]
#check Topology.IsConstructible.isRetrocompact
