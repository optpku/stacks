module

import StacksCheckRecall
public import ReasLib.RingTheory.Normal.Ring

@[expose] public section

/-!
# Normal Rings Are Integrally Closed

This source-facing file recalls the shared normal-ring bridge.

@stack 034M
-/

-- Lemma 10.37.12, tag `034M`: a normal ring is integrally closed in its total quotient ring.
@[stacks 034M "normal rings are integrally closed"]
#check @IsNormalRing.isIntegrallyClosed

@[stacks 034M "integrally closed instance"]
#check @IsNormalRing.instIsIntegrallyClosed
