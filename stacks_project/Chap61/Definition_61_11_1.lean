/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.WContractible
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 61.11.1: a commutative ring `A` is w-contractible if every
faithfully flat weakly étale ring map `A →+* B` has a retraction. -/
@[stacks 0981] #check (IsWContractibleRing : (A : Type u) → [CommRing A] → Prop)

#check isWContractibleRing_iff
#check IsWContractibleRing.exists_retraction
