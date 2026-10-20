/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module.Self
import StacksCheckRecall

@[expose] public section

/-!
# Maximal prime chains in a Cohen-Macaulay local ring

@stack 00N9
-/

/- Lemma 10.104.3: every maximal prime chain in a Noetherian local Cohen-Macaulay ring has
length equal to the Krull dimension of the ring. -/
@[stacks 00N9]
#check @Module.CohenMacaulay.length_eq_ringKrullDim_of_maximal_chain_self
