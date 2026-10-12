/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Regular.JRing.FiniteTypeDomain
import StacksCheckRecall

/-!
# Lemma 15.47.4

@stack 07PA
-/

@[expose] public section

/-! # Lemma 15.47.4: descent of J-0 for finite type domains -/

/- Lemma 15.47.4, tag `07PA`: `J-0` descends along an injective finite type map of domains. -/
@[stacks 07PA "descent of J-0 along an injective finite type map"]
#check @IsJ0Ring.FiniteTypeDomain.descend
