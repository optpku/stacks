/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.FaithfullyFlat.Projective
import StacksCheckRecall

@[expose] public section

/-!
# Theorem 10.95.6

@stack 05A9
-/

/- Theorem 10.95.6 [stacks 05A9]: canonical recall of faithfully flat descent
of projectivity for arbitrary modules. -/
@[stacks 05A9]
#check @Module.Projective.of_tensorProduct
