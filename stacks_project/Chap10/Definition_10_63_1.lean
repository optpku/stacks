/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.63.1

This chapter entry is a source-facing recall of the reusable exact-annihilator
associated-prime API. The neutral owner lives in
`ReasLib.RingTheory.Ideal.AssociatedPrime`.

@stack 00LA
-/

/- Definition 10.63.1: exact association is the predicate
`Ideal.IsAssociatedToModule`, and its set-valued owner is `associatedPrimesOfModule`. -/
@[stacks 00LA]
#check @Ideal.IsAssociatedToModule
@[stacks 00LA "associated-prime set owner"]
#check @associatedPrimesOfModule
