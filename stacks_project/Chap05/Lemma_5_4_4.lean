/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.SeparatedMap
import StacksCheckRecall

@[expose] public section

/- Canonical core: fiberwise separation is preserved by pullback without continuity assumptions. -/
@[stacks 0CY4 "separatedness is preserved by pullback"]
#check IsSeparatedMap.pullback
