/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RegularLocalRing.Domain
import StacksCheckRecall

/-!
# Lemma 10.106.2

@stack 00NP
-/

@[expose] public section

/- Lemma 10.106.2 [stacks 00NP]: the reusable domain instance for regular
local rings. -/
@[stacks 00NP]
#check @IsRegularLocalRing.isDomain
