/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.ZMod
import StacksCheckRecall

/-!
# Tensoring need not preserve injectivity

@stack 00DI
-/

@[expose] public section

@[stacks 00DI "the integer scalar map is injective"]
#check ZMod.modulus_linearMap_injective 2 (by decide)

@[stacks 00DI "tensoring the integer scalar map is not injective"]
#check ZMod.modulus_rTensor_not_injective 2 (by decide)

@[stacks 00DI "non-flat consequence"]
#check ZMod.not_flat 2 (by decide)
