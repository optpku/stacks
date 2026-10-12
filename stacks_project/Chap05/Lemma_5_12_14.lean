/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Noetherian.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.12.14

The compact-to-global permanence theorem is part of the reusable locally Noetherian API.
-/

/- Lemma 5.12.14: a compact locally Noetherian topological space is Noetherian. -/
@[stacks 04ZB]
#check @TopologicalSpace.LocallyNoetherianSpace.noetherianSpace
