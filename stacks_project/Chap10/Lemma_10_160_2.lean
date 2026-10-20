/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Completion.Finite
import StacksCheckRecall

@[expose] public section

/-! @stack 0325 -/

/-!
# Lemma 10.160.2

The two clauses belong to the complete-local-ring owner: quotient stability
is an instance-level fact, while the finite-algebra clause is the canonical
product map indexed by `Ideal.primesOver` together with its bijectivity.
-/

/- Lemma 10.160.2 (1), tag `0325`: a proper quotient of a Noetherian complete
local ring is complete local. -/
@[stacks 0325]
#check @IsCompleteLocalRing.quotient

/- Lemma 10.160.2 (2), tag `0325`: a finite algebra over a Noetherian complete
local ring maps bijectively to its completed local factors over the closed point. -/
@[stacks 0325]
#check @IsCompleteLocalRing.finiteProductMap
@[stacks 0325]
#check @IsCompleteLocalRing.finiteProductMap_apply
@[stacks 0325]
#check @IsCompleteLocalRing.finiteProductMap_bijective
